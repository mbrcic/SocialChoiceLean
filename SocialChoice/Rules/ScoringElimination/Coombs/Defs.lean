import SocialChoice.Rules.ScoringElimination.Defs

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

/-- The veto (anti-plurality) scoring vector: position r out of m candidates gets
    1 point unless it's the last position (r + 1 = m). -/
def vetoScore : Nat → Nat → Int :=
  fun m r => if r + 1 < m then 1 else 0

/-- Coombs' method (veto/anti-plurality elimination). -/
noncomputable def coombs : VotingRule :=
  scoringEliminationRule vetoScore

/-- Alias for Coombs' method. -/
noncomputable abbrev vetoElimination : VotingRule := coombs

end SocialChoice
