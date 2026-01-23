import SocialChoice.Rules.ScoringRules.Defs
import SocialChoice.Axioms.Independence
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open scoped BigOperators

theorem borda_independence_of_universally_least_preferred_nonempty :
    ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
      (P : Profile V A) (c d : A),
        c ≠ d →
          (∀ v : V, BottomRank P v d) →
            liftWinners (borda (restrictCandidates P (fun a => a ≠ d))) = borda P := by
  intro V A _ _ _ _ P c d hcd hbottom
  classical
  let P' := restrictCandidates P (fun a => a ≠ d)
  let score : Nat → Int := fun r => bordaScore (Fintype.card A) r
  let score' : Nat → Int := fun r => bordaScore (Fintype.card {a // a ≠ d}) r
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  have hA' : (Finset.univ : Finset {a // a ≠ d}).Nonempty := ⟨⟨c, hcd⟩, by simp⟩
  have hV : (Finset.univ : Finset V).Nonempty := by
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    exact ⟨v0, by simp⟩
  have hscore_voter (v : V) (a : A) (hne : a ≠ d) :
      score' (rank (P'.pref v) ⟨a, hne⟩) =
        score (rank (P.pref v) a) - 1 := by
    let below : Finset A :=
      (Finset.univ.filter (fun y => (P.pref v).lt a y))
    let below' : Finset {x : A // x ≠ d} :=
      (Finset.univ.filter (fun y => (P'.pref v).lt ⟨a, hne⟩ y))
    have hbelow_mem : d ∈ below := by
      have hbot : (P.pref v).lt a d := by
        simpa [Prefers] using (hbottom v a hne)
      exact Finset.mem_filter.mpr ⟨mem_univ _, hbot⟩
    have hlt_iff :
        ∀ y : {x : A // x ≠ d}, (P'.pref v).lt ⟨a, hne⟩ y ↔
          (P.pref v).lt a y.1 := by
      intro y
      rfl
    have himage : below'.image (fun y => y.1) = below.erase d := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
        have hy'lt : (P.pref v).lt a y' := (hlt_iff y').1 (Finset.mem_filter.mp hy').2
        exact Finset.mem_erase.mpr ⟨y'.2, Finset.mem_filter.mpr ⟨by simp, hy'lt⟩⟩
      · intro hy
        have hyne : y ≠ d := (Finset.mem_erase.mp hy).1
        have hylt : (P.pref v).lt a y := (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).2
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨y, hyne⟩, ?_, rfl⟩
        have hylt' : (P'.pref v).lt ⟨a, hne⟩ ⟨y, hyne⟩ := (hlt_iff ⟨y, hyne⟩).2 hylt
        exact Finset.mem_filter.mpr ⟨by simp, hylt'⟩
    have hinj : Function.Injective (fun y : {x : A // x ≠ d} => y.1) := by
      intro x y hxy
      ext
      exact hxy
    have hbelow_card : below'.card = below.card - 1 := by
      have hcard_image :=
        (Finset.card_image_of_injective (s := below') (f := fun y => y.1) hinj)
      have hcard' : below'.card = (below.erase d).card := by
        simpa [himage] using hcard_image.symm
      have hcard'' : (below.erase d).card = below.card - 1 := by
        simpa using (Finset.card_erase_of_mem (s := below) hbelow_mem)
      exact hcard'.trans hcard''
    have hpos : 1 ≤ below.card := by
      have hpos' : 0 < below.card := Finset.card_pos.mpr ⟨d, hbelow_mem⟩
      exact (Nat.succ_le_iff.2 hpos')
    have hscore' :
        score' (rank (P'.pref v) ⟨a, hne⟩) = Int.ofNat below'.card := by
      simpa [score', below', Prefers] using
        (bordaScore_eq_card_prefers (r := P'.pref v) (x := ⟨a, hne⟩))
    have hscore :
        score (rank (P.pref v) a) = Int.ofNat below.card := by
      simpa [score, below, Prefers] using
        (bordaScore_eq_card_prefers (r := P.pref v) (x := a))
    calc
      score' (rank (P'.pref v) ⟨a, hne⟩) = Int.ofNat below'.card := hscore'
      _ = Int.ofNat (below.card - 1) := by simp [hbelow_card]
      _ = (Int.ofNat below.card) - 1 := by
        simpa using (Int.ofNat_sub hpos)
      _ = score (rank (P.pref v) a) - 1 := by
        simp [hscore]
  have hscoreCandidate (a : A) (hne : a ≠ d) :
      scoreCandidate P' score' ⟨a, hne⟩ =
        scoreCandidate P score a - (Fintype.card V : Int) := by
    unfold scoreCandidate
    have hsum :
        (Finset.univ : Finset V).sum (fun v =>
            score' (rank (P'.pref v) ⟨a, hne⟩)) =
          (Finset.univ : Finset V).sum (fun v =>
            score (rank (P.pref v) a) - 1) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      exact hscore_voter v a hne
    calc
      (Finset.univ : Finset V).sum (fun v =>
          score' (rank (P'.pref v) ⟨a, hne⟩)) =
        (Finset.univ : Finset V).sum (fun v =>
          score (rank (P.pref v) a) - 1) := hsum
      _ =
        (Finset.univ : Finset V).sum (fun v =>
          score (rank (P.pref v) a)) -
          (Finset.univ : Finset V).sum (fun _v => (1 : Int)) := by
            simp [Finset.sum_sub_distrib]
      _ = scoreCandidate P score a - (Fintype.card V : Int) := by
            simp [scoreCandidate, Finset.sum_const]
  have horder (a b : A) (ha : a ≠ d) (hb : b ≠ d) :
      scoreCandidate P' score' ⟨b, hb⟩ ≤ scoreCandidate P' score' ⟨a, ha⟩ ↔
        scoreCandidate P score b ≤ scoreCandidate P score a := by
    have ha' := hscoreCandidate a ha
    have hb' := hscoreCandidate b hb
    constructor <;> intro h <;> linarith
  have hwinP (a : A) :
      a ∈ borda P ↔
        ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score a := by
    simpa [borda, scoringRule, score] using
      (scoringWinners_iff_forall_le (P := P) (score := score) (hA := hA) (c := a))
  have hwinP' (a : A) (hne : a ≠ d) :
      (⟨a, hne⟩ : {x : A // x ≠ d}) ∈ borda P' ↔
        ∀ b : {x : A // x ≠ d},
          scoreCandidate P' score' b ≤ scoreCandidate P' score' ⟨a, hne⟩ := by
    simpa [borda, scoringRule, score'] using
      (scoringWinners_iff_forall_le (P := P') (score := score') (hA := hA') (c := ⟨a, hne⟩))
  have hscore_d : scoreCandidate P score d = 0 := by
    unfold scoreCandidate
    have hzero : ∀ v : V, score (rank (P.pref v) d) = 0 := by
      intro v
      let below : Finset A :=
        (Finset.univ.filter (fun y => (P.pref v).lt d y))
      have hbelow_empty : below = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        let _ := P.pref v
        have hdy : (P.pref v).lt d y := (Finset.mem_filter.mp hy).2
        have hyd : (P.pref v).lt y d := by
          simpa [Prefers] using (hbottom v y (by simpa [eq_comm] using (ne_of_lt hdy)))
        exact (lt_asymm hdy hyd)
      have hscore_d' :
          score (rank (P.pref v) d) = Int.ofNat below.card := by
        simpa [score, below] using
          (bordaScore_eq_card_prefers (r := P.pref v) (x := d))
      simp [hscore_d', hbelow_empty]
    simp [hzero]
  have hscore_pos (a : A) (hne : a ≠ d) : 0 < scoreCandidate P score a := by
    unfold scoreCandidate
    have hpos_v : ∀ v : V, 0 < score (rank (P.pref v) a) := by
      intro v
      let below : Finset A :=
        (Finset.univ.filter (fun y => (P.pref v).lt a y))
      have hbelow_mem : d ∈ below := by
        have hbot : (P.pref v).lt a d := by
          simpa [Prefers] using (hbottom v a hne)
        exact Finset.mem_filter.mpr ⟨mem_univ _, hbot⟩
      have hcard_pos : 0 < below.card := Finset.card_pos.mpr ⟨d, hbelow_mem⟩
      have hscore' :
          score (rank (P.pref v) a) = Int.ofNat below.card := by
        simpa [score, below] using
          (bordaScore_eq_card_prefers (r := P.pref v) (x := a))
      have hpos_int : (0 : Int) < Int.ofNat below.card := by
        simpa using (Int.ofNat_lt.mpr hcard_pos)
      simpa [hscore'] using hpos_int
    have hsum_pos :
        0 < (Finset.univ : Finset V).sum (fun v => score (rank (P.pref v) a)) := by
      refine Finset.sum_pos (s := (Finset.univ : Finset V))
        (f := fun v => score (rank (P.pref v) a)) ?_ hV
      intro v hv
      exact hpos_v v
    simpa using hsum_pos
  have hscore_d_lt (a : A) (hne : a ≠ d) :
      scoreCandidate P score d < scoreCandidate P score a := by
    simpa [hscore_d] using hscore_pos a hne
  have hnot_winner : d ∉ borda P := by
    intro hd
    have hmax : ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score d :=
      (hwinP d).1 hd
    exact (not_lt_of_ge (hmax c)) (hscore_d_lt c hcd)
  apply Finset.ext
  intro a
  by_cases had : a = d
  · subst had
    have : a ∉ liftWinners (borda P') := by
      simp [liftWinners, P']
    constructor
    · intro ha
      exact (this ha).elim
    · intro ha
      exact (hnot_winner ha).elim
  · have hne : a ≠ d := had
    constructor
    · intro ha
      have ha' : ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ borda P' := by
        simpa [liftWinners, P'] using ha
      rcases ha' with ⟨hne', ha'⟩
      have hmax' :
          ∀ b : {x : A // x ≠ d},
            scoreCandidate P' score' b ≤ scoreCandidate P' score' ⟨a, hne'⟩ :=
        (hwinP' a hne').1 ha'
      have hmax : ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score a := by
        intro b
        by_cases hbd : b = d
        · subst hbd
          exact le_of_lt (hscore_d_lt a hne')
        · have hb := hmax' ⟨b, hbd⟩
          exact (horder a b hne' hbd).1 hb
      exact (hwinP a).2 hmax
    · intro ha
      have hmax : ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score a :=
        (hwinP a).1 ha
      have hne' : a ≠ d := by
        intro hEq
        subst hEq
        exact (hnot_winner ha).elim
      have hmax' :
          ∀ b : {x : A // x ≠ d},
            scoreCandidate P' score' b ≤ scoreCandidate P' score' ⟨a, hne'⟩ := by
        intro b
        have hb : scoreCandidate P score b.1 ≤ scoreCandidate P score a := hmax b.1
        exact (horder a b.1 hne' b.2).2 hb
      have ha' : (⟨a, hne'⟩ : {x : A // x ≠ d}) ∈ borda P' :=
        (hwinP' a hne').2 hmax'
      have ha'' : ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ borda P' := ⟨hne', ha'⟩
      simpa [liftWinners, P'] using ha''

end SocialChoice
