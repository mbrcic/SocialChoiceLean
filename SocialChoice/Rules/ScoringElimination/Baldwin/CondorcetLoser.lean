import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringElimination.Baldwin.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open scoped BigOperators

variable {V A : Type} [Fintype V] [Fintype A]

lemma one_lt_card_subtype_ne {A : Type} [Fintype A] [DecidableEq A] {c : A}
    (h : 2 < Fintype.card A) : 1 < Fintype.card {x : A // x ≠ c} := by
  have hpred : 1 < (Fintype.card A).pred := by
    have hle : 2 ≤ (Fintype.card A).pred := Nat.le_pred_of_lt h
    exact lt_of_lt_of_le (by decide : (1 : Nat) < 2) hle
  simpa [card_subtype_ne_eq c, Nat.pred_eq_sub_one] using hpred

lemma condorcet_loser_restrictProfile_of_two_lt_card
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {d c : A} (hdc : d ≠ c)
    (hcard : 2 < Fintype.card A) (hloser : condorcet_loser P d) :
    condorcet_loser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) := by
  classical
  refine ⟨?_, ?_⟩
  · intro y hy
    have hne : d ≠ (y : A) := by
      intro hEq
      apply hy
      ext
      simpa using hEq
    have hpos : margin_pos P (y : A) d := hloser.1 (y : A) hne
    dsimp [margin_pos] at hpos ⊢
    have heq := margin_eq_margin_restrictProfile (P := P) (c := c) (a := y)
      (b := (⟨d, hdc⟩ : {x : A // x ≠ c}))
    simpa [heq] using hpos
  · have hone : 1 < Fintype.card {x : A // x ≠ c} :=
      one_lt_card_subtype_ne (A := A) (c := c) hcard
    rcases Fintype.exists_ne_of_one_lt_card hone (⟨d, hdc⟩ : {x : A // x ≠ c}) with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩

lemma two_elems_eq_or_eq (hcard : Fintype.card A = 2) (a b : A) (hab : a ≠ b) (c : A) :
    c = a ∨ c = b := by
  classical
  have hpair : ({a, b} : Finset A).card = 2 := Finset.card_pair hab
  have hsub : ({a, b} : Finset A) ⊆ (Finset.univ : Finset A) := by
    intro x _
    exact Finset.mem_univ x
  have hcard_univ : (Finset.univ : Finset A).card = 2 := by
    simpa [Finset.card_univ] using hcard
  have hpair_eq : ({a, b} : Finset A) = (Finset.univ : Finset A) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hcard_univ, hpair]
  have huniv : (Finset.univ : Finset A) = {a, b} := hpair_eq.symm
  have hc : c ∈ ({a, b} : Finset A) := by
    simpa [huniv] using Finset.mem_univ c
  simpa using hc

lemma univ_erase_eq_singleton_of_card_two {A : Type} [Fintype A] [DecidableEq A]
    (hcard : Fintype.card A = 2) {c d : A} (hcd : c ≠ d) :
    (Finset.univ.erase d : Finset A) = {c} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ?_
  refine ⟨?mem, ?unique⟩
  · simp [hcd]
  · intro x hx
    have hxne : x ≠ d := (Finset.mem_erase.mp hx).1
    have hx_or : x = c ∨ x = d := two_elems_eq_or_eq (A := A) hcard c d hcd x
    cases hx_or with
    | inl hxc => exact hxc
    | inr hxd => exact (hxne hxd).elim

lemma c2BordaScore_pos_of_two_of_neg
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2) {c d : A} (hcd : c ≠ d)
    (hneg : c2BordaScore P d < 0) : 0 < c2BordaScore P c := by
  have hsum := c2BordaScore_sum_zero (P := P)
  have hsum' :
      (Finset.univ.erase d).sum (fun x => c2BordaScore P x) + c2BordaScore P d = 0 := by
    have hsum' :=
      Finset.sum_erase_add (s := (Finset.univ : Finset A))
        (f := fun x => c2BordaScore P x) (a := d) (by simp)
    rw [hsum] at hsum'
    exact hsum'
  have herase : (Finset.univ.erase d : Finset A) = {c} :=
    univ_erase_eq_singleton_of_card_two (A := A) hcard (c := c) (d := d) hcd
  have hsum'' : c2BordaScore P c + c2BordaScore P d = 0 := by
    simpa [herase] using hsum'
  linarith

lemma condorcet_loser_lower_borda_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (hloser : condorcet_loser P d) :
    scoreCandidate P (fun r => bordaScore 2 r) d <
      scoreCandidate P (fun r => bordaScore 2 r) c := by
  have hneg : c2BordaScore P d < 0 :=
    c2BordaScore_neg_of_condorcet_loser (P := P) (x := d) hloser
  have hpos : 0 < c2BordaScore P c :=
    c2BordaScore_pos_of_two_of_neg (P := P) (hcard := hcard) (c := c) (d := d) hcd hneg
  have hlt_c2 : c2BordaScore P d < c2BordaScore P c := lt_trans hneg hpos
  have hlt_borda :
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d <
        scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c :=
    (c2BordaScore_lt_iff_bordaScore_lt (P := P) (x := d) (y := c)).1 hlt_c2
  simpa [hcard] using hlt_borda

theorem baldwin_condorcet_loser_criterion : condorcet_loser_criterion baldwin := by
  intro V A _ _ P d hloser
  classical
  letI : DecidableEq A := Classical.decEq A
  change d ∉ scoringEliminationAux bordaScore A P
  set n : Nat := Fintype.card A
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
          condorcet_loser P d → d ∉ scoringEliminationAux bordaScore A P
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    intro A _ _ hcard V _ P d hloser
    classical
    have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
      intro hle
      have hsubs : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      rcases hloser.2 with ⟨y, hy⟩
      exact hy (Subsingleton.elim d y)
    by_cases htwo : Fintype.card A = 2
    · have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := bordaScore) (P := P) (hcard := hnot_le_one)
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      have hlt :
          scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d <
            scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c := by
        have hlt' :=
          condorcet_loser_lower_borda_two (V := V) (A := A) (P := P) (hcard := htwo)
            (c := c) (d := d) hcd hloser
        simpa [htwo] using hlt'
      have hle :
          scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c ≤
            scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d :=
        scoreCandidate_le_of_mem_lowestScoring (P := P)
          (score := fun r => bordaScore (Fintype.card A) r) (c := c) (e := d) hcL
      exact (not_lt_of_ge hle) hlt
    · have hgt2 : 2 < Fintype.card A := by
        have hne2 : Fintype.card A ≠ 2 := htwo
        have hone : 1 < Fintype.card A := Nat.lt_of_not_ge hnot_le_one
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hone) (Ne.symm hne2)
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := bordaScore) (P := P) (hcard := hnot_le_one)
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      have hdc : d ≠ c := by simpa [eq_comm] using hcd
      have hd_in' : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∈
          scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c) := by
        rcases (mem_liftFinset_iff_subtype
          (s := scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c))
          (x := d)).1 hd_in with ⟨hdc', hd_in'⟩
        simpa using hd_in'
      have hltcard : Fintype.card {x : A // x ≠ c} < k := by
        simpa [hcard] using (card_restrict_lt (A := A) c)
      have hloser' :
          condorcet_loser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) :=
        condorcet_loser_restrictProfile_of_two_lt_card (P := P) (hdc := hdc) (hcard := hgt2) hloser
      have hnot : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∉
          scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c) := by
        have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
          (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
          (d := (⟨d, hdc⟩ : {x : A // x ≠ c})) hloser'
        simpa using this
      exact hnot hd_in'
  exact hStrong (A := A) (by rfl) (V := V) (P := P) (d := d) hloser

end SocialChoice
