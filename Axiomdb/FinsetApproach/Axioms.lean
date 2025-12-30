import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Axiomdb.FinsetApproach.Profile

namespace FinsetApproach

open Finset

-- Helpers for counting voters.
noncomputable def votersPreferring (P : Profile) (a b : Agenda P) : Finset (Electorate P) := by
  classical
  exact P.voters.attach.filter (fun v => Prefers P v a b)

noncomputable def votersTop (P : Profile) (c : Agenda P) : Finset (Electorate P) := by
  classical
  exact P.voters.attach.filter (fun v => TopRank P v c)

noncomputable def votersBottom (P : Profile) (c : Agenda P) : Finset (Electorate P) := by
  classical
  exact P.voters.attach.filter (fun v => BottomRank P v c)

def StrictMajority (P : Profile) (S : Finset (Electorate P)) : Prop :=
  2 * S.card > P.voters.card

-- Candidate renaming on winner sets.
noncomputable def permuteWinners (P : Profile)
    (σ : Equiv.Perm (Agenda P))
    (s : Finset (Agenda P)) : Finset (Agenda P) := by
  classical
  exact s.map σ.toEmbedding

-- Ballot-level predicates used in variable-electorate axioms.
def BallotTop (P : Profile) (r : LinearOrder (Agenda P)) (c : Agenda P) : Prop :=
  ∀ d : Agenda P, d ≠ c → r.lt c d

def BallotBottom (P : Profile) (r : LinearOrder (Agenda P)) (c : Agenda P) : Prop :=
  ∀ d : Agenda P, d ≠ c → r.lt d c

-- Core axioms.
def Anonymity (f : VotingRule) : Prop :=
  ∀ (P : Profile) (σ : Equiv.Perm (Electorate P)), f (permuteVoters P σ) = f P

def Neutrality (f : VotingRule) : Prop :=
  ∀ (P : Profile) (σ : Equiv.Perm (Agenda P)),
    permuteWinners P σ (f P) = f (permuteCandidates P σ)

def Resolute (f : VotingRule) : Prop :=
  ∀ (P : Profile), (f P).card = 1

def NonTrivial (f : VotingRule) : Prop :=
  ∃ (P : Profile) (c : Agenda P), c ∉ f P

def Onto (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Cand) (hc : c ∈ P.candidates),
    ∃ (P' : Profile) (hC : P'.candidates = P.candidates),
      f P' = {⟨c, by simpa [hC] using hc⟩}

-- Efficiency axioms.
def ParetoEfficiency (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c d : Agenda P),
    (∀ v : Electorate P, Prefers P v c d) → d ∉ f P

def Unanimity (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P),
    (∀ v : Electorate P, TopRank P v c) → f P = {c}

-- Majoritarian axioms.
def MajorityCriterion (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P),
    StrictMajority P (votersTop P c) → f P = {c}

def MajorityLoserCriterion (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P),
    StrictMajority P (votersBottom P c) → c ∉ f P

def CondorcetWinner (P : Profile) (c : Agenda P) : Prop :=
  ∀ d : Agenda P, d ≠ c → StrictMajority P (votersPreferring P c d)

def CondorcetLoser (P : Profile) (c : Agenda P) : Prop :=
  ∀ d : Agenda P, d ≠ c → StrictMajority P (votersPreferring P d c)

def CondorcetConsistency (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P), CondorcetWinner P c → f P = {c}

def CondorcetLoserAvoidance (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P), CondorcetLoser P c → c ∉ f P

-- Variable-electorate axioms.
def PositiveInvolvement (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P) (v : Voter) (_hv : v ∉ P.voters)
      (ballot : LinearOrder (Agenda P)),
    c ∈ f P → BallotTop P ballot c → c ∈ f (addVoter P v ballot)

def NegativeInvolvement (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P) (v : Voter) (_hv : v ∉ P.voters)
      (ballot : LinearOrder (Agenda P)),
    c ∉ f P → BallotBottom P ballot c → c ∉ f (addVoter P v ballot)

-- Cast winners along an agenda equality.
noncomputable def castWinners {P₁ P₂ : Profile} (hC : P₁.candidates = P₂.candidates) :
    Finset (Agenda P₂) → Finset (Agenda P₁) := by
  intro s
  classical
  let hC' : P₂.candidates = P₁.candidates := hC.symm
  let e : Agenda P₂ ≃ Agenda P₁ := by
    refine
      { toFun := fun a => ⟨a.1, by simpa [hC'] using a.2⟩
        invFun := fun a => ⟨a.1, by simpa [hC] using a.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro a
      cases a
      rfl
    · intro a
      cases a
      rfl
  exact s.map e.toEmbedding

def Reinforcement (f : VotingRule) : Prop :=
  ∀ (P₁ P₂ : Profile) (hdisj : Disjoint P₁.voters P₂.voters)
      (hC : P₁.candidates = P₂.candidates),
    let f₂ := castWinners (P₁:=P₁) (P₂:=P₂) hC (f P₂);
    (f P₁ ∩ f₂).Nonempty →
      f (unionProfiles P₁ P₂ hdisj hC) = f P₁ ∪ f₂

def SubsetReinforcement (f : VotingRule) : Prop :=
  ∀ (P₁ P₂ : Profile) (hdisj : Disjoint P₁.voters P₂.voters)
      (hC : P₁.candidates = P₂.candidates),
    let f₂ := castWinners (P₁:=P₁) (P₂:=P₂) hC (f P₂);
    f P₁ ∩ f₂ ⊆ f (unionProfiles P₁ P₂ hdisj hC)

-- Lifting winners from a restricted agenda back to the original agenda.
noncomputable def liftWinners (P : Profile) (c : Cand) :
    Finset (Agenda (deleteCandidate P c)) → Finset (Agenda P) := by
  classical
  intro s
  exact s.image (fun a => ⟨a.1, (mem_erase.mp a.2).2⟩)

-- Variable-agenda axioms.
def IndependenceOfLosers (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c : Agenda P), c ∉ f P →
    liftWinners P c.1 (f (deleteCandidate P c.1)) = f P

def IndependenceOfDominated (f : VotingRule) : Prop :=
  ∀ (P : Profile) (c d : Agenda P),
    (∀ v : Electorate P, Prefers P v c d) →
      liftWinners P d.1 (f (deleteCandidate P d.1)) = f P

end FinsetApproach
