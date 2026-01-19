import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringRules.Veto.Defs
import SocialChoice.Meta

namespace SocialChoice

/-!
# Coombs' Method

Coombs' method is a scoring elimination rule based on anti-plurality (veto) scoring.

In each round, candidates are scored by the number of voters who do NOT rank them last.
Equivalently, each candidate receives 1 point from each voter except those who rank
them in the last position. The candidate(s) with the lowest score (i.e., the most
last-place rankings) are eliminated, and the process repeats until one candidate remains.

When there are ties for elimination, we use parallel-universe tie-breaking.
-/

/-- Coombs' method (veto/anti-plurality elimination). -/
@[scRule]
noncomputable def coombs : VotingRule :=
  scoringEliminationRule vetoScore

/-- Alias for Coombs' method. -/
noncomputable abbrev vetoElimination : VotingRule := coombs

end SocialChoice
