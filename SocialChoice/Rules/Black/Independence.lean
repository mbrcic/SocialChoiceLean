import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules.Black.Defs

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Black fails independence of dominated

Counterexample with 3 candidates (0,1,2) and 2 voters:
v0: 1 > 2 > 0
v1: 2 > 0 > 1
Candidate 2 Pareto-dominates 0.
Black selects {2}, but after removing 0, Black selects {1,2}.
-/

namespace BlackIndependenceCounterexample

def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | ⟨0, _⟩ => ballot120
  | ⟨1, _⟩ => ballot201

noncomputable def profile : Profile (Fin 2) (Fin 3) :=
  profileOfListBallots ballots

lemma prefers_2_0 : ∀ v : Fin 2, Prefers profile v (2 : Fin 3) (0 : Fin 3) := by
  intro v
  fin_cases v <;>
    simp [profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

noncomputable def profile' : Profile (Fin 2) {x : Fin 3 // x ≠ (0 : Fin 3)} :=
  restrictProfile profile (0 : Fin 3)

def cand1 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

lemma votersPreferring_profile_1_2 :
    votersPreferring profile (1 : Fin 3) (2 : Fin 3) = ({0} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_2_1 :
    votersPreferring profile (2 : Fin 3) (1 : Fin 3) = ({1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_0_2 :
    votersPreferring profile (0 : Fin 3) (2 : Fin 3) = (∅ : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma not_strictMajority_profile_1_2 :
    ¬ StrictMajority (votersPreferring profile (1 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_1_2]

lemma not_strictMajority_profile_2_1 :
    ¬ StrictMajority (votersPreferring profile (2 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_2_1]

lemma not_strictMajority_profile_0_2 :
    ¬ StrictMajority (votersPreferring profile (0 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_0_2]

lemma votersPreferring_restrict_cand1 :
    votersPreferring profile' cand1 cand2 = votersPreferring profile (1 : Fin 3) (2 : Fin 3) := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand1, cand2]

lemma votersPreferring_restrict_cand2 :
    votersPreferring profile' cand2 cand1 = votersPreferring profile (2 : Fin 3) (1 : Fin 3) := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand1, cand2]

lemma not_strictMajority_profile'_1_2 :
    ¬ StrictMajority (votersPreferring profile' cand1 cand2) := by
  simpa [votersPreferring_restrict_cand1] using not_strictMajority_profile_1_2

lemma not_strictMajority_profile'_2_1 :
    ¬ StrictMajority (votersPreferring profile' cand2 cand1) := by
  simpa [votersPreferring_restrict_cand2] using not_strictMajority_profile_2_1

lemma no_condorcet_profile : ¬ ∃ x, CondorcetWinner profile x := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile_0_2 hmaj).elim
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile_1_2 hmaj).elim
  · have hmaj := hx (1 : Fin 3) (by decide)
    exact (not_strictMajority_profile_2_1 hmaj).elim

lemma no_condorcet_profile' : ¬ ∃ x, CondorcetWinner profile' x := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases x with ⟨x, hxne⟩
  fin_cases x
  · cases hxne rfl
  · have hne : cand2 ≠ (⟨1, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
      intro hEq
      have hval : (2 : Fin 3) = 1 := by
        exact congrArg Subtype.val hEq
      cases hval
    have hmaj := hx cand2 hne
    have hx' : (⟨1, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1 := by
      apply Subtype.ext
      rfl
    have hmaj' : StrictMajority (votersPreferring profile' cand1 cand2) := by
      simpa [hx'] using hmaj
    exact (not_strictMajority_profile'_1_2 hmaj').elim
  · have hne : cand1 ≠ (⟨2, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
      intro hEq
      have hval : (1 : Fin 3) = 2 := by
        exact congrArg Subtype.val hEq
      cases hval
    have hmaj := hx cand1 hne
    have hx' : (⟨2, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand2 := by
      apply Subtype.ext
      rfl
    have hmaj' : StrictMajority (votersPreferring profile' cand2 cand1) := by
      simpa [hx'] using hmaj
    exact (not_strictMajority_profile'_2_1 hmaj').elim

lemma borda_profile_not_1 : (1 : Fin 3) ∉ borda profile := by
  decide

lemma borda_profile'_has_1 : cand1 ∈ borda profile' := by
  decide

lemma black_profile_not_1 : (1 : Fin 3) ∉ black profile := by
  have h : ¬ ∃ x, CondorcetWinner profile x := no_condorcet_profile
  simpa [black, h] using borda_profile_not_1

lemma black_profile'_has_1 : cand1 ∈ black profile' := by
  have h : ¬ ∃ x, CondorcetWinner profile' x := no_condorcet_profile'
  simpa [black, h] using borda_profile'_has_1

lemma lift_black_profile'_has_1 : (1 : Fin 3) ∈ liftWinners (black profile') := by
  have h : cand1 ∈ black profile' := black_profile'_has_1
  simpa [liftWinners, cand1] using h

end BlackIndependenceCounterexample

open BlackIndependenceCounterexample

theorem black_not_independenceOfDominated : ¬ IndependenceOfDominated black := by
  intro hind
  have hpref : ∀ v : Fin 2, Prefers profile v (2 : Fin 3) (0 : Fin 3) :=
    prefers_2_0
  have hEq := hind (P := profile) (c := (2 : Fin 3)) (d := (0 : Fin 3)) hpref
  have hmem :
      (1 : Fin 3) ∈
        liftWinners (black (restrictCandidates profile (fun a => a ≠ (0 : Fin 3)))) := by
    simpa [profile', restrictProfile] using lift_black_profile'_has_1
  have hmem' : (1 : Fin 3) ∈ black profile := by
    simpa [hEq] using hmem
  exact (black_profile_not_1 hmem').elim

end SocialChoice
