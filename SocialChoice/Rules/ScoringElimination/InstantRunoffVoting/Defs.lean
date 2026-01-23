import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Meta

namespace SocialChoice

/-!
# Instant Runoff Voting (IRV)

Instant Runoff Voting, also known as the Alternative Vote or Ranked Choice Voting,
is a scoring elimination rule based on plurality scoring.

In each round, candidates are scored by the number of voters who rank them first.
The candidate(s) with the lowest first-place votes are eliminated, and the process
repeats until one candidate remains.

When there are ties for elimination, we use parallel-universe tie-breaking.
-/

/-- Instant Runoff Voting (plurality elimination). -/
@[scRule]
noncomputable def instantRunoffVoting : VotingRule :=
  scoringEliminationRule pluralityScore

/-- Alias for IRV. -/
noncomputable abbrev irv : VotingRule := instantRunoffVoting

/-- Alias for IRV (Alternative Vote). -/
noncomputable abbrev alternativeVote : VotingRule := instantRunoffVoting

theorem instantRunoffVoting_isVotingRule : IsVotingRule instantRunoffVoting := by
  intro V A _ _ _ P
  classical
  simpa [instantRunoffVoting] using
    (scoringEliminationRule_isVotingRule (score := pluralityScore) (V := V) (A := A) (P := P))

theorem irv_isVotingRule : IsVotingRule irv := by
  intro V A _ _ _ P
  simpa [irv] using (instantRunoffVoting_isVotingRule (V := V) (A := A) (P := P))

theorem alternativeVote_isVotingRule : IsVotingRule alternativeVote := by
  intro V A _ _ _ P
  simpa [alternativeVote] using (instantRunoffVoting_isVotingRule (V := V) (A := A) (P := P))

end SocialChoice
