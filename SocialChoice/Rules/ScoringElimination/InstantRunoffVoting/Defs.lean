import SocialChoice.Rules.ScoringElimination.Defs
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

end SocialChoice
