import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SocialChoice.Margin
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.Defs

namespace SocialChoice

open Finset
open scoped BigOperators
open Classical

noncomputable def c2BordaScore {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) : Int := by
  classical
  exact (Finset.univ.sum (fun y => margin P x y))

noncomputable def c2BordaRule : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    by_cases h : (Finset.univ : Finset A).Nonempty
    · let maxScore : Int :=
        (Finset.univ.image (fun c => c2BordaScore P c)).max' (by
          simpa [Finset.Nonempty] using h)
      exact (Finset.univ.filter (fun c => c2BordaScore P c = maxScore))
    · exact ∅

lemma prefers_partition_card {A : Type*} [Fintype A] (r : LinearOrder A) (x : A) :
    (Finset.univ.filter (fun y => r.lt y x)).card +
        (Finset.univ.filter (fun y => r.lt x y)).card =
      Fintype.card A - 1 := by
  classical
  let _ := r
  have hdisjoint :
      Disjoint (Finset.univ.filter (fun y : A => y < x))
        (Finset.univ.filter (fun y : A => x < y)) := by
    refine Finset.disjoint_left.2 ?_
    intro y hy1 hy2
    have hy1' : y < x := (Finset.mem_filter.mp hy1).2
    have hy2' : x < y := (Finset.mem_filter.mp hy2).2
    exact (lt_asymm hy1' hy2')
  have hunion :
      (Finset.univ.filter (fun y : A => y < x)) ∪
          (Finset.univ.filter (fun y : A => x < y)) =
        Finset.univ.erase x := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · have hy' : y < x := (Finset.mem_filter.mp hy).2
        have hyne : y ≠ x := ne_of_lt hy'
        exact Finset.mem_erase.mpr ⟨hyne, by simp⟩
      · have hy' : x < y := (Finset.mem_filter.mp hy).2
        have hyne : y ≠ x := (ne_of_lt hy').symm
        exact Finset.mem_erase.mpr ⟨hyne, by simp⟩
    · intro hy
      have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
      have hlt_or_gt : y < x ∨ x < y := lt_or_gt_of_ne hyne
      cases hlt_or_gt with
      | inl hlt =>
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨by simp, hlt⟩))
      | inr hgt =>
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨by simp, hgt⟩))
  have hsum :
      (Finset.univ.filter (fun y : A => y < x)).card +
          (Finset.univ.filter (fun y : A => x < y)).card =
        (Finset.univ.erase x).card := by
    have hcard_union :
        ((Finset.univ.filter (fun y : A => y < x)) ∪
              (Finset.univ.filter (fun y : A => x < y))).card =
          (Finset.univ.filter (fun y : A => y < x)).card +
            (Finset.univ.filter (fun y : A => x < y)).card := by
      simpa using (Finset.card_union_of_disjoint hdisjoint)
    have hcard_union' :
        (Finset.univ.filter (fun y : A => y < x)).card +
            (Finset.univ.filter (fun y : A => x < y)).card =
          ((Finset.univ.filter (fun y : A => y < x)) ∪
                (Finset.univ.filter (fun y : A => x < y))).card := by
      simpa using hcard_union.symm
    simpa [hunion] using hcard_union'
  have hx : x ∈ (Finset.univ : Finset A) := by simp
  have herase : (Finset.univ.erase x).card = Fintype.card A - 1 := by
    simpa using (Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) hx)
  exact hsum.trans herase

lemma bordaScore_eq_card_prefers {A : Type*} [Fintype A] (r : LinearOrder A) (x : A) :
    bordaScore (Fintype.card A) (rank r x) =
      Int.ofNat ((Finset.univ.filter (fun y => r.lt x y)).card) := by
  classical
  have hsum := prefers_partition_card r x
  have hbelow :
      (Finset.univ.filter (fun y => r.lt x y)).card =
        Fintype.card A - 1 - rank r x := by
    have hsum' :
        (Finset.univ.filter (fun y => r.lt x y)).card +
            (Finset.univ.filter (fun y => r.lt y x)).card =
          Fintype.card A - 1 := by
      simpa [rank, Nat.add_comm] using hsum
    have hsum'' :
        (Finset.univ.filter (fun y => r.lt x y)).card =
          Fintype.card A - 1 - rank r x := by
      refine Nat.eq_sub_of_add_eq ?_
      simpa [rank] using hsum'
    exact hsum''
  simp [bordaScore, hbelow]

lemma c2BordaScore_eq_affine {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) :
    c2BordaScore P x =
      2 * scoreCandidate P (fun r => bordaScore (Fintype.card A) r) x -
        (Fintype.card V : Int) * ((Fintype.card A : Int) - 1) := by
  classical
  have hscore :
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) x =
        (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v hv
    simpa using (bordaScore_eq_card_prefers (r := P.pref v) (x := x))
  have hsum_pref :
      (Finset.univ : Finset A).sum (fun y =>
        Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt x y)).card)) =
      (Finset.univ : Finset V).sum (fun v =>
        Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
    have hsum_comm :
        (Finset.univ : Finset V).sum (fun v =>
          (Finset.univ : Finset A).sum (fun y => ite ((P.pref v).lt x y) (1 : Int) 0)) =
        (Finset.univ : Finset A).sum (fun y =>
          (Finset.univ : Finset V).sum (fun v => ite ((P.pref v).lt x y) (1 : Int) 0)) := by
      simpa using
        (Finset.sum_comm (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset A))
          (f := fun v y => ite ((P.pref v).lt x y) (1 : Int) 0))
    have hsum_left :
        (Finset.univ : Finset V).sum (fun v =>
          (Finset.univ : Finset A).sum (fun y => ite ((P.pref v).lt x y) (1 : Int) 0)) =
        (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simpa using
        (Finset.sum_boole (s := (Finset.univ : Finset A))
          (p := fun y => (P.pref v).lt x y))
    have hsum_right :
        (Finset.univ : Finset A).sum (fun y =>
          (Finset.univ : Finset V).sum (fun v => ite ((P.pref v).lt x y) (1 : Int) 0)) =
        (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt x y)).card)) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      simpa using
        (Finset.sum_boole (s := (Finset.univ : Finset V))
          (p := fun v => (P.pref v).lt x y))
    calc
      (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt x y)).card)) =
          (Finset.univ : Finset A).sum (fun y =>
            (Finset.univ : Finset V).sum (fun v => ite ((P.pref v).lt x y) (1 : Int) 0)) := by
              symm
              exact hsum_right
      _ =
          (Finset.univ : Finset V).sum (fun v =>
            (Finset.univ : Finset A).sum (fun y => ite ((P.pref v).lt x y) (1 : Int) 0)) := by
              simpa using hsum_comm.symm
      _ =
          (Finset.univ : Finset V).sum (fun v =>
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := hsum_left
  have hsum_pref_rev :
      (Finset.univ : Finset A).sum (fun y =>
        Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt y x)).card)) =
      (Finset.univ : Finset V).sum (fun v =>
        Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) := by
    have hsum_comm :
        (Finset.univ : Finset V).sum (fun v =>
          (Finset.univ : Finset A).sum (fun y => ite ((P.pref v).lt y x) (1 : Int) 0)) =
        (Finset.univ : Finset A).sum (fun y =>
          (Finset.univ : Finset V).sum (fun v => ite ((P.pref v).lt y x) (1 : Int) 0)) := by
      simpa using
        (Finset.sum_comm (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset A))
          (f := fun v y => ite ((P.pref v).lt y x) (1 : Int) 0))
    have hsum_left :
        (Finset.univ : Finset V).sum (fun v =>
          (Finset.univ : Finset A).sum (fun y => ite ((P.pref v).lt y x) (1 : Int) 0)) =
        (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simpa using
        (Finset.sum_boole (s := (Finset.univ : Finset A))
          (p := fun y => (P.pref v).lt y x))
    have hsum_right :
        (Finset.univ : Finset A).sum (fun y =>
          (Finset.univ : Finset V).sum (fun v => ite ((P.pref v).lt y x) (1 : Int) 0)) =
        (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt y x)).card)) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      simpa using
        (Finset.sum_boole (s := (Finset.univ : Finset V))
          (p := fun v => (P.pref v).lt y x))
    calc
      (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt y x)).card)) =
          (Finset.univ : Finset A).sum (fun y =>
            (Finset.univ : Finset V).sum (fun v => ite ((P.pref v).lt y x) (1 : Int) 0)) := by
              symm
              exact hsum_right
      _ =
          (Finset.univ : Finset V).sum (fun v =>
            (Finset.univ : Finset A).sum (fun y => ite ((P.pref v).lt y x) (1 : Int) 0)) := by
              simpa using hsum_comm.symm
      _ =
          (Finset.univ : Finset V).sum (fun v =>
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) := hsum_left
  have hcard_rev :
      (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) =
        (Fintype.card V : Int) * ((Fintype.card A : Int) - 1) -
          (Finset.univ : Finset V).sum (fun v =>
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
    have hcard_v :
        ∀ v : V,
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card) =
            (Fintype.card A : Int) - 1 -
              Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card) := by
      intro v
      have hnat :
          (Finset.univ.filter (fun y => (P.pref v).lt x y)).card +
              (Finset.univ.filter (fun y => (P.pref v).lt y x)).card =
            Fintype.card A - 1 := by
        have h := prefers_partition_card (r := P.pref v) (x := x)
        simpa [Nat.add_comm] using h
      have hint :
          (Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card) +
              Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card) : Int) =
            (Fintype.card A : Int) - 1 := by
        have hint' :
            (((Finset.univ.filter (fun y => (P.pref v).lt x y)).card +
                (Finset.univ.filter (fun y => (P.pref v).lt y x)).card : Nat) : Int) =
              Int.ofNat (Fintype.card A - 1) :=
          congrArg (fun n : Nat => (n : Int)) hnat
        have hpos : 1 ≤ Fintype.card A := by
          let _ : Nonempty A := ⟨x⟩
          exact Nat.succ_le_iff.2 Fintype.card_pos
        simpa [Nat.cast_add, Int.ofNat_sub hpos] using hint'
      linarith
    have hsum_v :
        (Finset.univ : Finset V).sum (fun v =>
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) =
          (Finset.univ : Finset V).sum (fun v =>
            (Fintype.card A - 1 : Int) -
              Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      exact hcard_v v
    calc
      (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) =
        (Finset.univ : Finset V).sum (fun v =>
          (Fintype.card A : Int) - 1 -
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := hsum_v
      _ =
        (Finset.univ : Finset V).sum (fun _v => (Fintype.card A : Int) - 1) -
          (Finset.univ : Finset V).sum (fun v =>
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
          simpa [Finset.sum_sub_distrib]
      _ =
        (Fintype.card V : Int) * ((Fintype.card A : Int) - 1) -
          (Finset.univ : Finset V).sum (fun v =>
            Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) := by
          simp [Finset.sum_const]
          ring
  have hfilter_card (y : A) :
      (@Finset.filter V (fun v => (P.pref v).lt x y)
            (fun v => Classical.propDecidable ((P.pref v).lt x y))
            (Finset.univ : Finset V)).card =
        (Finset.univ.filter (fun v => (P.pref v).lt x y)).card := by
    classical
    simpa using
      congrArg Finset.card
        (Finset.filter_congr_decidable (s := (Finset.univ : Finset V))
          (p := fun v => (P.pref v).lt x y)
          (h := fun v => Classical.propDecidable ((P.pref v).lt x y)))
  have hfilter_card_rev (y : A) :
      (@Finset.filter V (fun v => (P.pref v).lt y x)
            (fun v => Classical.propDecidable ((P.pref v).lt y x))
            (Finset.univ : Finset V)).card =
        (Finset.univ.filter (fun v => (P.pref v).lt y x)).card := by
    classical
    simpa using
      congrArg Finset.card
        (Finset.filter_congr_decidable (s := (Finset.univ : Finset V))
          (p := fun v => (P.pref v).lt y x)
          (h := fun v => Classical.propDecidable ((P.pref v).lt y x)))
  have hmargin :
      c2BordaScore P x =
        (Finset.univ : Finset A).sum (fun y =>
            Int.ofNat
              ((@Finset.filter V (fun v => (P.pref v).lt x y)
                    (fun v => Classical.propDecidable ((P.pref v).lt x y))
                    (Finset.univ : Finset V)).card)) -
          (Finset.univ : Finset A).sum (fun y =>
            Int.ofNat
              ((@Finset.filter V (fun v => (P.pref v).lt y x)
                    (fun v => Classical.propDecidable ((P.pref v).lt y x))
                    (Finset.univ : Finset V)).card)) := by
    classical
    simp [c2BordaScore, margin, Prefers, Finset.sum_sub_distrib]
  calc
    c2BordaScore P x =
      (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat
            ((@Finset.filter V (fun v => (P.pref v).lt x y)
                  (fun v => Classical.propDecidable ((P.pref v).lt x y))
                  (Finset.univ : Finset V)).card)) -
        (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat
            ((@Finset.filter V (fun v => (P.pref v).lt y x)
                  (fun v => Classical.propDecidable ((P.pref v).lt y x))
                  (Finset.univ : Finset V)).card)) := hmargin
    _ =
      (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt x y)).card)) -
        (Finset.univ : Finset A).sum (fun y =>
          Int.ofNat ((Finset.univ.filter (fun v => (P.pref v).lt y x)).card)) := by
        simp [hfilter_card, hfilter_card_rev]
    _ =
      (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) -
        (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt y x)).card)) := by
        rw [hsum_pref, hsum_pref_rev]
    _ =
      2 * (Finset.univ : Finset V).sum (fun v =>
          Int.ofNat ((Finset.univ.filter (fun y => (P.pref v).lt x y)).card)) -
        (Fintype.card V : Int) * ((Fintype.card A : Int) - 1) := by
        linarith [hcard_rev]
    _ =
      2 * scoreCandidate P (fun r => bordaScore (Fintype.card A) r) x -
        (Fintype.card V : Int) * ((Fintype.card A : Int) - 1) := by
        simpa [hscore]

theorem borda_eq_c2BordaRule {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) : borda P = c2BordaRule P := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let scoreSet : Finset Int :=
      (Finset.univ.image
        (fun c => scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c))
    let maxScore : Int :=
      scoreSet.max' (by
        simpa [scoreSet, Finset.Nonempty] using
          (h.image (fun c =>
            scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c)))
    let const : Int := (Fintype.card V : Int) * ((Fintype.card A : Int) - 1)
    let f : Int → Int := fun z => 2 * z - const
    let maxMargin : Int :=
      (scoreSet.image f).max' (by
        simpa [scoreSet, f, Finset.Nonempty] using
          (h.image (fun c =>
            f (scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c))))
    have hmarginScore :
        ∀ c,
          c2BordaScore P c =
            f (scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c) := by
      intro c
      simpa [f, const] using (c2BordaScore_eq_affine (P := P) (x := c))
    have hmaxMargin : maxMargin = f maxScore := by
      have hscoreSet : scoreSet.Nonempty := by
        simpa [scoreSet] using
          (h.image (fun c =>
            scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c))
      have hmono : Monotone f := by
        intro a b hab
        linarith
      have hmap :
          f (scoreSet.max' hscoreSet) = (scoreSet.image f).max' (hscoreSet.image f) := by
        simpa using (Monotone.map_finset_max' (f := f) hmono (s := scoreSet) hscoreSet)
      simpa [maxScore, maxMargin] using hmap.symm
    have himage :
        (Finset.univ.image (fun c => c2BordaScore P c)) = scoreSet.image f := by
      ext z
      constructor
      · intro hz
        rcases Finset.mem_image.mp hz with ⟨c, hc, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
        · simpa [hmarginScore c]
      · intro hz
        rcases Finset.mem_image.mp hz with ⟨z0, hz0, rfl⟩
        rcases Finset.mem_image.mp hz0 with ⟨c, hc, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨c, hc, ?_⟩
        symm
        simpa [hmarginScore c]
    ext c
    constructor <;> intro hc
    · have hc' :
          scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c = maxScore := by
          simpa [borda, scoringRule, scoringWinners, h, scoreSet, maxScore] using hc
      have :
          c2BordaScore P c = maxMargin := by
        simpa [hmarginScore c, hmaxMargin, hc'] using (rfl : f maxScore = f maxScore)
      simpa [c2BordaRule, h, scoreSet, maxMargin, himage] using this
    · have hc' :
          c2BordaScore P c = maxMargin := by
          simpa [c2BordaRule, h, scoreSet, maxMargin, himage] using hc
      have :
          scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c = maxScore := by
        have hc'' : f (scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c) = f maxScore := by
          simpa [hmarginScore c, hmaxMargin] using hc'
        -- f is affine with nonzero slope, so injective
        linarith
      simpa [borda, scoringRule, scoringWinners, h, scoreSet, maxScore] using this
  · unfold borda scoringRule c2BordaRule scoringWinners
    simp [h]

lemma c2BordaScore_pos_of_condorcet_winner {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hwin : condorcet_winner P x) (hne : ∃ y, y ≠ x) :
    0 < c2BordaScore P x := by
  classical
  rcases hne with ⟨y, hy⟩
  have hnonempty : (Finset.univ.erase x : Finset A).Nonempty := by
    exact ⟨y, by simp [hy]⟩
  have hpos :
      0 < (Finset.univ.erase x : Finset A).sum (fun y => margin P x y) := by
    refine (Finset.sum_pos (s := (Finset.univ.erase x : Finset A))
      (f := fun y => margin P x y) ?_ hnonempty)
    intro y hy
    have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
    have hyne' : x ≠ y := by simpa [eq_comm] using hyne
    have hxy : 0 < margin P x y := by
      simpa [margin_pos] using hwin y hyne'
    exact hxy
  have hsum :
      c2BordaScore P x =
        (Finset.univ.erase x : Finset A).sum (fun y => margin P x y) := by
    have hsum' :=
      (Finset.sum_erase_add (s := (Finset.univ : Finset A))
        (f := fun y => margin P x y) (a := x) (by simp)).symm
    have hx0 : margin P x x = 0 := self_margin_zero (P := P) (a := x)
    simpa [c2BordaScore, hx0] using hsum'
  simpa [hsum] using hpos

lemma c2BordaScore_neg_of_condorcet_loser {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hlose : condorcet_loser P x) :
    c2BordaScore P x < 0 := by
  classical
  rcases hlose with ⟨hlose, ⟨y, hy⟩⟩
  have hnonempty : (Finset.univ.erase x : Finset A).Nonempty := by
    exact ⟨y, by simpa [eq_comm] using hy⟩
  have hpos :
      0 < (Finset.univ.erase x : Finset A).sum (fun y => margin P y x) := by
    refine (Finset.sum_pos (s := (Finset.univ.erase x : Finset A))
      (f := fun y => margin P y x) ?_ hnonempty)
    intro y hy
    have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
    have hyne' : x ≠ y := by simpa [eq_comm] using hyne
    have hxy : 0 < margin P y x := by
      simpa [margin_pos] using hlose y hyne'
    exact hxy
  have hsum :
      c2BordaScore P x =
        (Finset.univ.erase x : Finset A).sum (fun y => margin P x y) := by
    have hsum' :=
      (Finset.sum_erase_add (s := (Finset.univ : Finset A))
        (f := fun y => margin P x y) (a := x) (by simp)).symm
    have hx0 : margin P x x = 0 := self_margin_zero (P := P) (a := x)
    simpa [c2BordaScore, hx0] using hsum'
  have hskew : ∀ y, margin P x y = - margin P y x := by
    intro y
    simpa [skew_symmetric] using (margin_antisymmetric (P := P) x y)
  have hsum_neg :
      c2BordaScore P x =
        - (Finset.univ.erase x : Finset A).sum (fun y => margin P y x) := by
    calc
      c2BordaScore P x =
          (Finset.univ.erase x : Finset A).sum (fun y => margin P x y) := hsum
      _ =
          (Finset.univ.erase x : Finset A).sum (fun y => - margin P y x) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            exact hskew y
      _ =
          - (Finset.univ.erase x : Finset A).sum (fun y => margin P y x) := by
            simp [Finset.sum_neg_distrib]
  have hneg :
      - (Finset.univ.erase x : Finset A).sum (fun y => margin P y x) < 0 := by
    simpa using (neg_neg_of_pos hpos)
  simpa [hsum_neg] using hneg

lemma c2BordaScore_sum_zero {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) :
    (Finset.univ : Finset A).sum (fun x => c2BordaScore P x) = 0 := by
  classical
  have hskew : ∀ x y, margin P y x = - margin P x y := by
    intro x y
    simpa [skew_symmetric] using (margin_antisymmetric (P := P) y x)
  have hswap :
      (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P x y)) =
        (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P y x)) := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset A))
        (f := fun x y => margin P x y))
  have hneg :
      (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P x y)) =
        - (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P x y)) := by
    calc
      (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P x y)) =
        (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P y x)) := hswap
      _ =
        (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => - margin P x y)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        refine Finset.sum_congr rfl ?_
        intro y hy
        exact hskew x y
      _ =
        - (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P x y)) := by
        simp [Finset.sum_neg_distrib]
  have hsum :
      (Finset.univ : Finset A).sum (fun x =>
          (Finset.univ : Finset A).sum (fun y => margin P x y)) = 0 := by
    linarith
  simpa [c2BordaScore] using hsum

lemma c2BordaRule_score_nonneg {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) {x : A} (hx : x ∈ c2BordaRule P) :
    0 ≤ c2BordaScore P x := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let scoreSet : Finset Int :=
      (Finset.univ.image (fun c => c2BordaScore P c))
    let maxScore : Int :=
      scoreSet.max' (by
        simpa [scoreSet, Finset.Nonempty] using
          (h.image (fun c => c2BordaScore P c)))
    have hx' : c2BordaScore P x = maxScore := by
      simpa [c2BordaRule, h, scoreSet, maxScore] using hx
    have hmax_nonneg : 0 ≤ maxScore := by
      by_contra hmax_nonneg
      have hmax_neg : maxScore < 0 := lt_of_not_ge hmax_nonneg
      have hscore_neg :
          ∀ c ∈ (Finset.univ : Finset A), c2BordaScore P c < 0 := by
        intro c hc
        have hmem : c2BordaScore P c ∈ scoreSet := by
          exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
        have hle : c2BordaScore P c ≤ maxScore := by
          exact Finset.le_max' scoreSet (c2BordaScore P c) hmem
        exact lt_of_le_of_lt hle hmax_neg
      have hsum_neg :
          (Finset.univ : Finset A).sum (fun c => c2BordaScore P c) < 0 := by
        refine Finset.sum_neg (s := (Finset.univ : Finset A)) ?_ h
        intro c hc
        exact hscore_neg c hc
      have hsum_zero := c2BordaScore_sum_zero (P := P)
      have : (0 : Int) < 0 := by
        simpa [hsum_zero] using hsum_neg
      exact (lt_irrefl 0 this)
    simpa [hx'] using hmax_nonneg
  · have : False := by
      simpa [c2BordaRule, h] using hx
    exact this.elim

end SocialChoice
