import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Axiomdb.FintypeApproach.Profile

namespace FintypeApproach

universe u

open Finset

-- Helpers for counting voters.
noncomputable def votersPreferring {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Prefers P v a b)

noncomputable def votersTop {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => TopRank P v c)

noncomputable def votersBottom {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => BottomRank P v c)

def StrictMajority {V : Type*} [Fintype V] (S : Finset V) : Prop :=
  2 * S.card > Fintype.card V

-- Candidate renaming on winner sets.
noncomputable def permuteWinners {A : Type*} (σ : Equiv.Perm A) (s : Finset A) : Finset A := by
  classical
  exact s.map σ.toEmbedding

-- Ballot-level predicates used in variable-electorate axioms.
def BallotTop {A : Type*} (r : LinearOrder A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → r.lt c d

def BallotBottom {A : Type*} (r : LinearOrder A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → r.lt d c

-- Core axioms.
def Anonymity (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (σ : Equiv.Perm V),
    f (permuteVoters P σ) = f P

def Neutrality (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (σ : Equiv.Perm A),
    permuteWinners σ (f P) = f (permuteCandidates P σ)

def Resolute (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A), (f P).card = 1

def NonTrivial (f : VotingRule) : Prop :=
  ∃ (V A : Type*) (instV : Fintype V) (instA : Fintype A),
    let _ := instV
    let _ := instA
    ∃ (P : Profile V A) (c : A), c ∉ f P

def Onto (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (c : A), ∃ P : Profile V A, f P = {c}

-- Efficiency axioms.
def ParetoEfficiency (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c d : A),
    (∀ v : V, Prefers P v c d) → d ∉ f P

def Unanimity (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    (∀ v : V, TopRank P v c) → f P = {c}

-- Majoritarian axioms.
def MajorityCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    StrictMajority (votersTop P c) → f P = {c}

def MajorityLoserCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    StrictMajority (votersBottom P c) → c ∉ f P

def CondorcetWinner {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → StrictMajority (votersPreferring P c d)

def CondorcetLoser {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → StrictMajority (votersPreferring P d c)

def CondorcetConsistency (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    CondorcetWinner P c → f P = {c}

def CondorcetLoserAvoidance (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    CondorcetLoser P c → c ∉ f P

-- Variable-electorate axioms.
def PositiveInvolvement (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (ballot : LinearOrder A),
    c ∈ f P → BallotTop ballot c → c ∈ f (addVoter P ballot)

def NegativeInvolvement (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (ballot : LinearOrder A),
    c ∉ f P → BallotBottom ballot c → c ∉ f (addVoter P ballot)

def Reinforcement (f : VotingRule) : Prop :=
  ∀ {V W A : Type u} [Fintype V] [Fintype W] [Fintype A] [DecidableEq A]
      (P₁ : Profile V A) (P₂ : Profile W A),
    (f P₁ ∩ f P₂).Nonempty →
      f (unionProfiles P₁ P₂) = f P₁ ∪ f P₂

def SubsetReinforcement (f : VotingRule) : Prop :=
  ∀ {V W A : Type u} [Fintype V] [Fintype W] [Fintype A] [DecidableEq A]
      (P₁ : Profile V A) (P₂ : Profile W A),
    f P₁ ∩ f P₂ ⊆ f (unionProfiles P₁ P₂)

-- Variable-agenda axioms.
noncomputable def liftWinners {A : Type*}
    {p : A → Prop} [DecidablePred p]
    (s : Finset {a // p a}) : Finset A := by
  classical
  exact s.image (fun a => a.1)

def IndependenceOfLosers (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A) (c : A),
    c ∉ f P →
      liftWinners (f (restrictCandidates P (fun a => a ≠ c))) = f P

def IndependenceOfDominated (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A) (c d : A),
    (∀ v : V, Prefers P v c d) →
      liftWinners (f (restrictCandidates P (fun a => a ≠ d))) = f P

end FintypeApproach
