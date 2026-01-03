import SocialChoice.Axioms.Participation
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules

namespace SocialChoice

open Finset

-- Plurality satisfies positive involvement.
theorem plurality_positiveInvolvement : PositiveInvolvement plurality := by
  intro V A _ _ P c ballot hc htop
  classical
  let P' := addVoter P ballot
  have ballot_not_top : ∀ d : A, d ≠ c → ¬ BallotTop ballot d := by
    intro d hne htopd
    have hcd : ballot.lt c d := htop d hne
    have hdc : ballot.lt d c := htopd c (by simpa [eq_comm] using hne)
    let _ : Preorder A := ballot.toPreorder
    exact (lt_asymm (a := c) (b := d) hcd) hdc
  let rightTop : A → Finset Unit :=
    fun d => if BallotTop ballot d then {()} else ∅
  have votersTop_addVoter :
      ∀ d : A, votersTop P' d = (votersTop P d).disjSum (rightTop d) := by
    intro d
    ext v
    cases v with
    | inl v =>
        simp [votersTop, P', addVoter, TopRank, Prefers, rightTop, Finset.inl_mem_disjSum]
    | inr u =>
        cases u
        have hL : Sum.inr PUnit.unit ∈ votersTop P' d ↔ BallotTop ballot d := by
          simp [votersTop, P', addVoter, TopRank, Prefers, BallotTop]
        by_cases hbt : BallotTop ballot d
        · simp [hL, rightTop, hbt, Finset.inr_mem_disjSum]
        · simp [hL, rightTop, hbt]
  have topCount_addVoter :
      ∀ d : A, topCount P' d = topCount P d + (rightTop d).card := by
    intro d
    unfold topCount
    simp [votersTop_addVoter, Finset.card_disjSum]
  have topCount_c : topCount P' c = topCount P c + 1 := by
    have : rightTop c = {()} := by
      simp [rightTop, htop]
    simpa [this] using topCount_addVoter c
  have topCount_ne : ∀ d : A, d ≠ c → topCount P' d = topCount P d := by
    intro d hne
    have : rightTop d = ∅ := by
      simp [rightTop, ballot_not_top d hne]
    simpa [this] using topCount_addVoter d
  have hmax_old : ∀ d : A, topCount P d ≤ topCount P c := by
    have hc' : c ∈ (Finset.univ.filter
        (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
      simpa [plurality] using hc
    exact (mem_filter.mp hc').2
  have hmax_new : ∀ d : A, topCount P' d ≤ topCount P' c := by
    intro d
    by_cases hne : d = c
    · simp [hne]
    · calc
        topCount P' d = topCount P d := topCount_ne d hne
        _ ≤ topCount P c := hmax_old d
        _ ≤ topCount P c + 1 := Nat.le_succ _
        _ = topCount P' c := topCount_c.symm
  have hc' : c ∈ (Finset.univ.filter
      (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) := by
    exact mem_filter.mpr ⟨mem_univ _, hmax_new⟩
  simpa [plurality] using hc'

end SocialChoice
