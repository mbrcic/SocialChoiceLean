import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Axiomdb.FintypeApproach.Axioms

namespace FintypeApproach

open Finset
open scoped BigOperators

-- Rank of a candidate in a ballot: number of candidates strictly above it.
def rank {A : Type*} [Fintype A] (r : LinearOrder A) (c : A) : Nat :=
  (Finset.univ.filter (fun d => r.lt d c)).card

-- Total score for a candidate under a scoring vector.
def scoreCandidate {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) (c : A) : Int :=
  ((Finset.univ : Finset V).sum fun v => score (rank (P.pref v) c))

-- Winners for a given scoring vector.
noncomputable def scoringWinners {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) : Finset A := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int :=
      (Finset.univ.image (fun c => scoreCandidate P score c)).max' (by
        simpa [Finset.Nonempty] using h)
    exact
      (Finset.univ.filter (fun c => scoreCandidate P score c = maxScore))
  · exact ∅

-- Generic positional scoring rule.
noncomputable def scoringRule (score : Nat → Nat → Int) : VotingRule :=
  fun {V A} _ _ (P : Profile V A) =>
    scoringWinners P (fun r => score (Fintype.card A) r)

-- Standard scoring vectors.
def pluralityScore (_m r : Nat) : Int := if r = 0 then 1 else 0

def vetoScore (m r : Nat) : Int := if r = m - 1 then 0 else 1

def bordaScore (m r : Nat) : Int := Int.ofNat (m - 1 - r)

noncomputable def topCount {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Nat :=
  (votersTop P c).card

-- Concrete rules.
noncomputable def trivialRule : VotingRule :=
  fun {V A} _ _ (_ : Profile V A) => (Finset.univ : Finset A)

noncomputable def plurality : VotingRule :=
  fun {V A} _ _ (P : Profile V A) =>
    (Finset.univ.filter (fun c => ∀ d : A, topCount P d ≤ topCount P c))

noncomputable def veto : VotingRule :=
  scoringRule vetoScore

noncomputable def borda : VotingRule :=
  scoringRule bordaScore

end FintypeApproach
