import SocialChoice.Examples
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Core
import SocialChoice.Axioms.Strategyproofness
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

namespace SocialChoice

open Finset

/-- List ballots for the 3-candidate cycle. -/
private def ballot012 : ListBallot 3 := ListBallot.identity 3
private def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
private def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
private def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
private def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
private def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

private def cycleBallots : Fin 3 → ListBallot 3
  | 0 => ballot012
  | 1 => ballot120
  | 2 => ballot201

private noncomputable def cycleProfile : Profile (Fin 3) (Fin 3) :=
  profileOfListBallots cycleBallots

private def swap0Ballots : Fin 3 → ListBallot 3
  | 0 => ballot021
  | 1 => ballot120
  | 2 => ballot201

private noncomputable def swap0Profile : Profile (Fin 3) (Fin 3) :=
  profileOfListBallots swap0Ballots

private def swap1Ballots : Fin 3 → ListBallot 3
  | 0 => ballot012
  | 1 => ballot102
  | 2 => ballot201

private noncomputable def swap1Profile : Profile (Fin 3) (Fin 3) :=
  profileOfListBallots swap1Ballots

private def swap2Ballots : Fin 3 → ListBallot 3
  | 0 => ballot012
  | 1 => ballot120
  | 2 => ballot210

private noncomputable def swap2Profile : Profile (Fin 3) (Fin 3) :=
  profileOfListBallots swap2Ballots

private lemma votersPreferring_card_eq_countPrefers {m n : ℕ}
    (ballots : Fin m → ListBallot n) (a b : Fin n) :
    (votersPreferring (profileOfListBallots ballots) a b).card =
    countPrefers (fun v => (ballots v).ranking) a b := by
  unfold countPrefers
  rw [votersPreferring_eq_filter_prefersInList]

private lemma strictMajority_fin3 {S : Finset (Fin 3)} (hcard : S.card = 2) :
    StrictMajority S := by
  unfold StrictMajority
  simp [hcard]

private lemma profile_ext {V A : Type} [Fintype V] [Fintype A]
    {P Q : Profile V A} (h : P.pref = Q.pref) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

private lemma swap0_CondorcetWinner : CondorcetWinner swap0Profile (2 : Fin 3) := by
  intro d hd
  fin_cases d
  · have hcount : countPrefers (fun v => (swap0Ballots v).ranking) 2 0 = 2 := rfl
    have hcard : (votersPreferring swap0Profile 2 0).card = 2 := by
      simpa [swap0Profile, votersPreferring_card_eq_countPrefers] using hcount
    exact strictMajority_fin3 hcard
  · have hcount : countPrefers (fun v => (swap0Ballots v).ranking) 2 1 = 2 := rfl
    have hcard : (votersPreferring swap0Profile 2 1).card = 2 := by
      simpa [swap0Profile, votersPreferring_card_eq_countPrefers] using hcount
    exact strictMajority_fin3 hcard
  · cases hd rfl

private lemma swap1_CondorcetWinner : CondorcetWinner swap1Profile (0 : Fin 3) := by
  intro d hd
  fin_cases d
  · cases hd rfl
  · have hcount : countPrefers (fun v => (swap1Ballots v).ranking) 0 1 = 2 := rfl
    have hcard : (votersPreferring swap1Profile 0 1).card = 2 := by
      simpa [swap1Profile, votersPreferring_card_eq_countPrefers] using hcount
    exact strictMajority_fin3 hcard
  · have hcount : countPrefers (fun v => (swap1Ballots v).ranking) 0 2 = 2 := rfl
    have hcard : (votersPreferring swap1Profile 0 2).card = 2 := by
      simpa [swap1Profile, votersPreferring_card_eq_countPrefers] using hcount
    exact strictMajority_fin3 hcard

private lemma swap2_CondorcetWinner : CondorcetWinner swap2Profile (1 : Fin 3) := by
  intro d hd
  fin_cases d
  · have hcount : countPrefers (fun v => (swap2Ballots v).ranking) 1 0 = 2 := rfl
    have hcard : (votersPreferring swap2Profile 1 0).card = 2 := by
      simpa [swap2Profile, votersPreferring_card_eq_countPrefers] using hcount
    exact strictMajority_fin3 hcard
  · cases hd rfl
  · have hcount : countPrefers (fun v => (swap2Ballots v).ranking) 1 2 = 2 := rfl
    have hcard : (votersPreferring swap2Profile 1 2).card = 2 := by
      simpa [swap2Profile, votersPreferring_card_eq_countPrefers] using hcount
    exact strictMajority_fin3 hcard

private lemma update_swap0_eq_cycle :
    updateProfile swap0Profile 0 ballot012.toLinearOrder = cycleProfile := by
  apply profile_ext
  funext v
  fin_cases v <;>
    simp [updateProfile, swap0Profile, cycleProfile, swap0Ballots, cycleBallots, profileOfListBallots]

private lemma update_swap1_eq_cycle :
    updateProfile swap1Profile 1 ballot120.toLinearOrder = cycleProfile := by
  apply profile_ext
  funext v
  fin_cases v <;>
    simp [updateProfile, swap1Profile, cycleProfile, swap1Ballots, cycleBallots, profileOfListBallots]

private lemma update_swap2_eq_cycle :
    updateProfile swap2Profile 2 ballot201.toLinearOrder = cycleProfile := by
  apply profile_ext
  funext v
  fin_cases v <;>
    simp [updateProfile, swap2Profile, cycleProfile, swap2Ballots, cycleBallots, profileOfListBallots]

private lemma voter0_prefers0_over2 : Prefers swap0Profile 0 0 2 := by
  simp [swap0Profile, swap0Ballots, prefers_iff_prefersInList, prefersInList]
  decide

private lemma voter1_prefers1_over0 : Prefers swap1Profile 1 1 0 := by
  simp [swap1Profile, swap1Ballots, prefers_iff_prefersInList, prefersInList]
  decide

private lemma voter2_prefers2_over1 : Prefers swap2Profile 2 2 1 := by
  simp [swap2Profile, swap2Ballots, prefers_iff_prefersInList, prefersInList]
  decide

theorem no_resolute_condorcet_strategyproof_3x3
    (f : VotingRule) (hf : Resolute f) :
    CondorcetConsistency f → ResoluteStrategyproofness f hf → False := by
  intro hcond hsp
  have hcard : (f cycleProfile).card = 1 := by
    simpa using (hf cycleProfile)
  rcases Finset.card_eq_one.mp hcard with ⟨x, hx⟩
  fin_cases x
  · have hcond0 : f swap0Profile = {2} := by
      simpa using (hcond swap0Profile 2 swap0_CondorcetWinner)
    have hnot :
        ¬ Prefers swap0Profile 0 0 2 :=
      hsp swap0Profile 0 ballot012.toLinearOrder 2 0 hcond0
        (by simpa [update_swap0_eq_cycle] using hx)
    exact hnot voter0_prefers0_over2
  · have hcond1 : f swap1Profile = {0} := by
      simpa using (hcond swap1Profile 0 swap1_CondorcetWinner)
    have hnot :
        ¬ Prefers swap1Profile 1 1 0 :=
      hsp swap1Profile 1 ballot120.toLinearOrder 0 1 hcond1
        (by simpa [update_swap1_eq_cycle] using hx)
    exact hnot voter1_prefers1_over0
  · have hcond2 : f swap2Profile = {1} := by
      simpa using (hcond swap2Profile 1 swap2_CondorcetWinner)
    have hnot :
        ¬ Prefers swap2Profile 2 2 1 :=
      hsp swap2Profile 2 ballot201.toLinearOrder 1 2 hcond2
        (by simpa [update_swap2_eq_cycle] using hx)
    exact hnot voter2_prefers2_over1

end SocialChoice
