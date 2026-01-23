import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringRules.Borda.Defs
import SocialChoice.Meta

namespace SocialChoice

/-!
# Baldwin's Method

Baldwin's method is a scoring elimination rule based on Borda scoring.

In each round, candidates are scored using the Borda count (where a candidate
ranked in position r out of m candidates receives m - 1 - r points from that voter).
The candidate(s) with the lowest Borda score are eliminated, and the process
repeats until one candidate remains.

When there are ties for elimination, we use parallel-universe tie-breaking.
-/

/-- Baldwin's method (Borda elimination). -/
@[scRule]
noncomputable def baldwin : VotingRule :=
  scoringEliminationRule bordaScore

/-- Alias for Baldwin's method. -/
noncomputable abbrev bordaElimination : VotingRule := baldwin

theorem baldwin_isVotingRule : IsVotingRule baldwin := by
  intro V A _ _ _ P
  classical
  simpa [baldwin] using
    (scoringEliminationRule_isVotingRule (score := bordaScore) (V := V) (A := A) (P := P))

theorem bordaElimination_isVotingRule : IsVotingRule bordaElimination := by
  intro V A _ _ _ P
  simpa [bordaElimination] using (baldwin_isVotingRule (V := V) (A := A) (P := P))

end SocialChoice
