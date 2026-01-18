import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Rank
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

/-!
# Common Lemmas for Veto and Coombs

This file contains lemmas shared between Veto scoring and Coombs elimination,
relating to bottom ranks and veto scores.
-/

lemma rank_eq_card_sub_one_iff_bottomRank
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (v : V) (c : A) :
    rank (P.pref v) c = Fintype.card A - 1 ↔ BottomRank P v c := by
  classical
  let r := P.pref v
  have hsubset : (Finset.univ.filter (fun d => r.lt d c)) ⊆ (Finset.univ.erase c) := by
    intro d hd
    have hd' : r.lt d c := (Finset.mem_filter.mp hd).2
    have hdc : d ≠ c := by
      intro hdc
      subst hdc
      exact lt_irrefl _ hd'
    exact Finset.mem_erase.mpr ⟨hdc, by simp⟩
  constructor
  · intro hrank d hdc
    have hcard :
        (Finset.univ.filter (fun d => r.lt d c)).card =
          (Finset.univ.erase c).card := by
      simpa [rank] using hrank
    have hEq : (Finset.univ.filter (fun d => r.lt d c)) = (Finset.univ.erase c) := by
      apply Finset.eq_of_subset_of_card_le hsubset
      simp [hcard]
    have hdmem : d ∈ (Finset.univ.erase c) := by
      exact Finset.mem_erase.mpr ⟨hdc, by simp⟩
    have hdmem' : d ∈ (Finset.univ.filter (fun d => r.lt d c)) := by
      simpa [hEq] using hdmem
    exact (Finset.mem_filter.mp hdmem').2
  · intro hbottom
    have hEq : (Finset.univ.filter (fun d => r.lt d c)) = (Finset.univ.erase c) := by
      ext d
      constructor
      · intro hd
        have hd' : r.lt d c := (Finset.mem_filter.mp hd).2
        have hdc : d ≠ c := by
          intro hdc
          subst hdc
          exact lt_irrefl _ hd'
        exact Finset.mem_erase.mpr ⟨hdc, by simp⟩
      · intro hd
        have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
        have hlt : r.lt d c := hbottom d hdc
        exact Finset.mem_filter.mpr ⟨by simp, hlt⟩
    simp [rank, hEq]

lemma vetoScore_scoreCandidate_eq_notBottom_card
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A)
    [DecidablePred (fun v => BottomRank P v c)]
    [DecidablePred (fun v => ¬ BottomRank P v c)] :
    scoreCandidate P (fun r => if r = Fintype.card A - 1 then 0 else 1) c =
      ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
  have hrank : ∀ v, (rank (P.pref v) c = Fintype.card A - 1) ↔ BottomRank P v c := by
    intro v
    simpa using (rank_eq_card_sub_one_iff_bottomRank (P := P) (v := v) (c := c))
  have heq :
      (∑ v : V, (fun r => if r = Fintype.card A - 1 then (0 : Int) else 1) (rank (P.pref v) c)) =
        ∑ v : V, if BottomRank P v c then (0 : Int) else 1 := by
    apply Finset.sum_congr rfl
    intro v _
    simp [hrank v]
  have hsum :
      (∑ v : V, if BottomRank P v c then (0 : Int) else 1) =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
    have hsum' :
        (∑ v : V, if BottomRank P v c then (0 : Int) else 1) =
          (Finset.univ.filter (fun v => ¬ BottomRank P v c)).sum (fun _ => (1 : Int)) := by
      have h :=
        (Finset.sum_filter (s := (Finset.univ : Finset V))
          (p := fun v => ¬ BottomRank P v c)
          (f := fun _ => (1 : Int)))
      have h' :
          (∑ v : V, if BottomRank P v c then (0 : Int) else 1) =
            ∑ v : V, if ¬ BottomRank P v c then (1 : Int) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hbc : BottomRank P v c
        · simp [hbc]
        · simp [hbc]
      exact h'.trans h.symm
    have hsum'' :
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).sum (fun _ => (1 : Int)) =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
      simp
    exact hsum'.trans hsum''
  have hscore : scoreCandidate P (fun r => if r = Fintype.card A - 1 then 0 else 1) c =
      ∑ v : V, if BottomRank P v c then (0 : Int) else 1 := by
    simpa [scoreCandidate] using heq
  calc
    scoreCandidate P (fun r => if r = Fintype.card A - 1 then 0 else 1) c
        = ∑ v : V, if BottomRank P v c then (0 : Int) else 1 := hscore
    _ = ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := hsum

lemma bottomRank_imp_not_bottomRank
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {c d : A} (hcd : c ≠ d) (v : V) :
    BottomRank P v c → ¬ BottomRank P v d := by
  intro hbc hbd
  have hdc : Prefers P v d c := hbc d hcd.symm
  have hcd' : Prefers P v c d := hbd c (by simpa [eq_comm] using hcd)
  let _ : Preorder A := (P.pref v).toPreorder
  exact lt_asymm hcd' hdc

end SocialChoice
