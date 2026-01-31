import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Meta

namespace SocialChoice

open Finset

section Copeland

variable {V A : Type} [Fintype V] [Fintype A]

/-- Double the usual Copeland score to avoid fractions: win = 2, tie = 1, loss = 0. -/
def copelandPairScore2 (m : Int) : Int :=
  if m > 0 then 2 else if m = 0 then 1 else 0

lemma copelandPairScore2_le_two (m : Int) : copelandPairScore2 m ≤ 2 := by
  by_cases hpos : m > 0
  · simp [copelandPairScore2, hpos]
  · by_cases hzero : m = 0
    · simp [copelandPairScore2, hzero]
    · simp [copelandPairScore2, hpos, hzero]

/-- Copeland score for a candidate, using doubled points. -/
noncomputable def copelandScore2 (P : Profile V A) (a : A) : Int := by
  classical
  exact Finset.sum Finset.univ (fun b => copelandPairScore2 (margin P a b))

/-- Maximum Copeland score (doubled) in a profile. -/
noncomputable def copelandMaxScore2 (P : Profile V A) : Int := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
    have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 P a)
    exact Finset.max' scores hScores
  · exact 0

@[scRule]
noncomputable def copeland : VotingRule := by
  intro V A _ _ P
  classical
  if hA : Nonempty A then
    let maxScore := copelandMaxScore2 (V := V) (A := A) P
    exact Finset.univ.filter (fun a => copelandScore2 P a = maxScore)
  else
    exact ∅

theorem copeland_isVotingRule : IsVotingRule copeland := by
  intro V A _ _ _ P
  classical
  have hAuniv : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
  have hScores : scores.Nonempty := hAuniv.image (fun a => copelandScore2 P a)
  let maxScore : Int := Finset.max' scores hScores
  have hmaxmem : maxScore ∈ scores := Finset.max'_mem scores hScores
  rcases Finset.mem_image.mp hmaxmem with ⟨a, ha, hscore⟩
  have hmem :
      a ∈ Finset.univ.filter (fun a => copelandScore2 P a = maxScore) := by
    exact Finset.mem_filter.mpr ⟨by simp [ha], hscore⟩
  have hA : Nonempty A := inferInstance
  have hmax_eq : copelandMaxScore2 (V := V) (A := A) P = maxScore := by
    simp [copelandMaxScore2, hAuniv, scores, maxScore]
  refine ⟨a, ?_⟩
  simpa [copeland, hA, hmax_eq] using hmem

end Copeland

end SocialChoice
