import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Axiomdb.FinsetApproach.Axioms

namespace FinsetApproach

open Finset
open scoped BigOperators
open scoped BigOperators

-- Rank of a candidate in a ballot: number of candidates strictly above it.
def rank (P : Profile) (r : LinearOrder (Agenda P)) (c : Agenda P) : Nat :=
  (P.candidates.attach.filter (fun d => r.lt d c)).card

-- Total score for a candidate under a scoring vector.
def scoreCandidate (P : Profile) (score : Nat → Int) (c : Agenda P) : Int :=
  (P.voters.attach.sum fun v => score (rank P (P.pref v) c))

-- Winners for a given scoring vector.
noncomputable def scoringWinners (P : Profile) (score : Nat → Int) : Finset (Agenda P) := by
  classical
  by_cases h : P.candidates.Nonempty
  · let maxScore : Int :=
      (P.candidates.attach.image (fun c => scoreCandidate P score c)).max' (by
        simpa [Finset.Nonempty] using h)
    exact
      P.candidates.attach.filter (fun c => scoreCandidate P score c = maxScore)
  · exact ∅

-- Generic positional scoring rule.
noncomputable def scoringRule (score : Nat → Nat → Int) : VotingRule :=
  fun P => scoringWinners P (fun r => score P.candidates.card r)

-- Standard scoring vectors.
def pluralityScore (_m r : Nat) : Int := if r = 0 then 1 else 0

def vetoScore (m r : Nat) : Int := if r = m - 1 then 0 else 1

def bordaScore (m r : Nat) : Int := Int.ofNat (m - 1 - r)

noncomputable def topCount (P : Profile) (c : Agenda P) : Nat :=
  (votersTop P c).card

-- Concrete rules.
noncomputable def trivialRule : VotingRule :=
  fun P => P.candidates.attach

noncomputable def plurality : VotingRule :=
  fun P =>
    P.candidates.attach.filter (fun c => ∀ d : Agenda P, topCount P d ≤ topCount P c)

noncomputable def veto : VotingRule :=
  scoringRule vetoScore

noncomputable def borda : VotingRule :=
  scoringRule bordaScore

end FinsetApproach
