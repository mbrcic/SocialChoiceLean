import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic

namespace FintypeApproach

open Finset


structure Profile (V A : Type*) [Fintype V] [Fintype A] where
  pref : V → LinearOrder A

abbrev VotingRule :=
  ∀ {V A : Type*} [Fintype V] [Fintype A], Profile V A → Finset A

def IsVotingRule (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A), (f P).Nonempty

-- Basic preference predicates.
def Prefers {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (a b : A) : Prop :=
  (P.pref v).lt a b

def TopRank {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) : Prop :=
  ∀ d : A, d ≠ c → Prefers P v c d

def BottomRank {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) : Prop :=
  ∀ d : A, d ≠ c → Prefers P v d c

-- Permute voters by relabeling the electorate.
def permuteVoters {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) : Profile V A :=
  { pref := fun v => P.pref (σ v) }

-- Relabel a linear order along a permutation.
noncomputable def relabelBallot {α : Type*} (r : LinearOrder α) (σ : Equiv.Perm α) : LinearOrder α := by
  classical
  let _ := r
  exact LinearOrder.lift' σ σ.injective

-- Permute candidates by relabeling each ballot.
noncomputable def permuteCandidates {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) : Profile V A :=
  { pref := fun v => relabelBallot (P.pref v) σ }

-- Add a voter via a sum type.
def addVoter {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) : Profile (V ⊕ Unit) A :=
  { pref := fun v =>
      match v with
      | Sum.inl v => P.pref v
      | Sum.inr _ => ballot }

-- Union of profiles on disjoint electorates using a sum type.
def unionProfiles {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (P₁ : Profile V A) (P₂ : Profile W A) : Profile (V ⊕ W) A :=
  { pref := fun v =>
      match v with
      | Sum.inl v => P₁.pref v
      | Sum.inr w => P₂.pref w }

-- Restrict the agenda by a predicate.
noncomputable def restrictBallot {A : Type*} (r : LinearOrder A)
    (p : A → Prop) [DecidablePred p] : LinearOrder {a // p a} := by
  classical
  let _ := r
  infer_instance

noncomputable def restrictCandidates {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p] : Profile V {a // p a} :=
  { pref := fun v => restrictBallot (P.pref v) p }

-- Tie back to ℕ via finite subtypes.
abbrev NatElectorate (S : Finset Nat) := {n // n ∈ S}
abbrev NatAgenda (S : Finset Nat) := {n // n ∈ S}

instance (S : Finset Nat) : Fintype (NatElectorate S) := by
  classical
  simpa [NatElectorate] using (Fintype.subtype S (by intro x; rfl))

instance (S : Finset Nat) : Fintype (NatAgenda S) := by
  classical
  simpa [NatAgenda] using (Fintype.subtype S (by intro x; rfl))

abbrev ProfileOnNat (V A : Finset Nat) := Profile (NatElectorate V) (NatAgenda A)

end FintypeApproach
