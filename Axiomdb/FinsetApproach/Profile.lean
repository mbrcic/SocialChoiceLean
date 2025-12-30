import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

namespace FinsetApproach

open Finset


abbrev Voter := Nat
abbrev Cand := Nat

structure Profile where
  voters : Finset Voter
  candidates : Finset Cand
  pref : {v // v ∈ voters} → LinearOrder {a // a ∈ candidates}

abbrev Electorate (P : Profile) := {v // v ∈ P.voters}
abbrev Agenda (P : Profile) := {a // a ∈ P.candidates}

abbrev VotingRule := (P : Profile) → Finset (Agenda P)

def IsVotingRule (f : VotingRule) : Prop :=
  ∀ P, (f P).Nonempty

-- Basic preference predicates.
def Prefers (P : Profile) (v : Electorate P) (a b : Agenda P) : Prop :=
  (P.pref v).lt a b

def TopRank (P : Profile) (v : Electorate P) (c : Agenda P) : Prop :=
  ∀ d : Agenda P, d ≠ c → Prefers P v c d

def BottomRank (P : Profile) (v : Electorate P) (c : Agenda P) : Prop :=
  ∀ d : Agenda P, d ≠ c → Prefers P v d c

-- Permute voters by relabeling the electorate.
def permuteVoters (P : Profile) (σ : Equiv.Perm (Electorate P)) : Profile :=
  { voters := P.voters
    candidates := P.candidates
    pref := fun v => P.pref (σ v) }

-- Relabel a linear order along a permutation.
-- This uses `LinearOrder.lift` to pull back the order via σ.
noncomputable def relabelBallot {α : Type*} (r : LinearOrder α) (σ : Equiv.Perm α) : LinearOrder α := by
  classical
  let _ := r
  exact LinearOrder.lift' σ σ.injective

-- Permute candidates by relabeling each ballot.
noncomputable def permuteCandidates (P : Profile) (σ : Equiv.Perm (Agenda P)) : Profile :=
  { voters := P.voters
    candidates := P.candidates
    pref := fun v => relabelBallot (P.pref v) σ }

-- Add one voter with a specified ballot.
noncomputable def addVoter (P : Profile) (v : Voter)
    (ballot : LinearOrder (Agenda P)) : Profile := by
  classical
  refine
    { voters := insert v P.voters
      candidates := P.candidates
      pref := ?_ }
  intro w
  by_cases h : (w : Voter) = v
  · simpa [h] using ballot
  · have hw : (w : Voter) ∈ P.voters := by
      have hw' : (w : Voter) ∈ insert v P.voters := w.property
      rcases mem_insert.mp hw' with hw' | hw'
      · exact (False.elim (h hw'))
      · exact hw'
    exact P.pref ⟨w, hw⟩

-- Union of profiles on disjoint electorates with the same candidate set.
noncomputable def unionProfiles (P₁ P₂ : Profile)
    (_hdisj : Disjoint P₁.voters P₂.voters)
    (hC : P₁.candidates = P₂.candidates) : Profile := by
  classical
  refine
    { voters := P₁.voters ∪ P₂.voters
      candidates := P₁.candidates
      pref := ?_ }
  intro v
  by_cases h : (v : Voter) ∈ P₁.voters
  · exact P₁.pref ⟨v, h⟩
  · have hv' : (v : Voter) ∈ P₂.voters := by
      have hv' : (v : Voter) ∈ P₁.voters ∪ P₂.voters := v.property
      rcases mem_union.mp hv' with hv' | hv'
      · exact (False.elim (h hv'))
      · exact hv'
    have hC' : P₂.candidates = P₁.candidates := hC.symm
    let e : Agenda P₁ ≃ Agenda P₂ := by
      refine
        { toFun := fun a => ⟨a.1, by simpa [hC] using a.2⟩
          invFun := fun a => ⟨a.1, by simpa [hC'] using a.2⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro a
        cases a
        rfl
      · intro a
        cases a
        rfl
    let _ := P₂.pref ⟨v, hv'⟩
    exact LinearOrder.lift' e e.injective

-- Delete a candidate by restricting each ballot.
noncomputable def deleteCandidate (P : Profile) (c : Cand) : Profile := by
  classical
  let incl : {a // a ∈ P.candidates.erase c} → {a // a ∈ P.candidates} :=
    fun a => ⟨a.1, (mem_erase.mp a.2).2⟩
  have hinj : Function.Injective incl := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  refine
    { voters := P.voters
      candidates := P.candidates.erase c
      pref := ?_ }
  intro v
  let _ := P.pref v
  exact LinearOrder.lift' incl hinj

end FinsetApproach
