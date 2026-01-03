import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import SocialChoice.Axioms.Pareto
import SocialChoice.Rank
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset

theorem scoringRule_pareto_nonempty (score : Nat → Nat → Int)
    (hstrict : strictlyDecreasingScore score) :
    ParetoEfficiencyNonempty (scoringRule score) := by
  intro V A _ _ _ P c d hpref hd
  classical
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
  have hlt :
      scoreCandidate P scoreFun d < scoreCandidate P scoreFun c := by
    unfold scoreCandidate
    have hle :
        ∀ v ∈ (Finset.univ : Finset V),
          scoreFun (rank (P.pref v) d) ≤ scoreFun (rank (P.pref v) c) := by
      intro v hv
      have hlt_rank : rank (P.pref v) c < rank (P.pref v) d :=
        rank_lt_of_lt (r := P.pref v) (c := c) (d := d) (hpref v)
      exact (hstrict (Fintype.card A) _ _ hlt_rank).le
    have hlt' :
        ∃ v ∈ (Finset.univ : Finset V),
          scoreFun (rank (P.pref v) d) < scoreFun (rank (P.pref v) c) := by
      rcases Classical.choice (inferInstance : Nonempty V) with v0
      refine ⟨v0, by simp, ?_⟩
      have hlt_rank : rank (P.pref v0) c < rank (P.pref v0) d :=
        rank_lt_of_lt (r := P.pref v0) (c := c) (d := d) (hpref v0)
      exact hstrict (Fintype.card A) _ _ hlt_rank
    exact Finset.sum_lt_sum hle hlt'
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  let scoreSet : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate P scoreFun c))
  let maxScore : Int :=
    scoreSet.max' (by
      simpa [scoreSet, Finset.Nonempty] using hA)
  have hle_max : scoreCandidate P scoreFun c ≤ maxScore := by
    have hmem : scoreCandidate P scoreFun c ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    exact Finset.le_max' scoreSet _ hmem
  have hlt_max : scoreCandidate P scoreFun d < maxScore :=
    lt_of_lt_of_le hlt hle_max
  have hd' : scoreCandidate P scoreFun d = maxScore := by
    have hd' : d ∈ scoringWinners P scoreFun := by
      simpa [scoringRule, scoreFun] using hd
    simpa [scoringWinners, hA, scoreSet, maxScore] using hd'
  exact (ne_of_lt hlt_max) hd'

end SocialChoice
