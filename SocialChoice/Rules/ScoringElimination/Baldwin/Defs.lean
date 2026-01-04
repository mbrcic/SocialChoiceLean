import SocialChoice.Rules.ScoringElimination.Defs

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

/-- The Borda scoring vector: position r out of m candidates gets m - 1 - r points. -/
def bordaScore' : Nat → Nat → Int :=
  fun m r => (m : Int) - 1 - r

/-- Baldwin's method (Borda elimination). -/
noncomputable def baldwin : VotingRule :=
  scoringEliminationRule bordaScore'

/-- Alias for Baldwin's method. -/
noncomputable abbrev bordaElimination : VotingRule := baldwin

end SocialChoice
