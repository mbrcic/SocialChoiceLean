import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Monotonicity
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs

namespace SocialChoice

open Finset

open Classical

/-!
# Plurality with Runoff (and IRV) fails monotonicity

We use a 17-voter profile with three candidates. Candidate 0 wins plurality with
runoff; after two voters lift 0 to the top (without changing the relative order
of the other candidates), candidate 0 loses.
-/

namespace PluralityWithRunoffMonotonicityCounterexample

private noncomputable def pairC (x y : Fin 3) : Finset (Fin 3) := by
  letI : DecidableEq (Fin 3) := Classical.decEq (Fin 3)
  exact insert x ({y} : Finset (Fin 3))

private lemma pairC_eq_pair (x y : Fin 3) : pairC x y = ({x, y} : Finset (Fin 3)) := by
  classical
  ext z
  simp [pairC, Finset.mem_insert, Finset.mem_singleton]

def ballot012 : ListBallot 3 := ListBallot.mk' [0, 1, 2]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]

def ballots : Fin 17 -> ListBallot 3
  | 0 => ballot012
  | 1 => ballot012
  | 2 => ballot012
  | 3 => ballot012
  | 4 => ballot012
  | 5 => ballot012
  | 6 => ballot102
  | 7 => ballot102
  | 8 => ballot102
  | 9 => ballot102
  | 10 => ballot102
  | 11 => ballot210
  | 12 => ballot210
  | 13 => ballot210
  | 14 => ballot210
  | 15 => ballot210
  | 16 => ballot210
  | _ => ballot210

def ballots' : Fin 17 -> ListBallot 3
  | 0 => ballot012
  | 1 => ballot012
  | 2 => ballot012
  | 3 => ballot012
  | 4 => ballot012
  | 5 => ballot012
  | 6 => ballot102
  | 7 => ballot102
  | 8 => ballot102
  | 9 => ballot102
  | 10 => ballot102
  | 11 => ballot210
  | 12 => ballot210
  | 13 => ballot210
  | 14 => ballot210
  | 15 => ballot021
  | 16 => ballot021
  | _ => ballot021

noncomputable def profile : Profile (Fin 17) (Fin 3) :=
  profileOfListBallots ballots

noncomputable def profile' : Profile (Fin 17) (Fin 3) :=
  profileOfListBallots ballots'

private lemma topCount_profile_0 : topCount profile (0 : Fin 3) = 6 := by
  have hcount : countTop (fun v => (ballots v).ranking) 0 = 6 := rfl
  have hcard : (votersTop profile (0 : Fin 3)).card = 6 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_1 : topCount profile (1 : Fin 3) = 5 := by
  have hcount : countTop (fun v => (ballots v).ranking) 1 = 5 := rfl
  have hcard : (votersTop profile (1 : Fin 3)).card = 5 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_2 : topCount profile (2 : Fin 3) = 6 := by
  have hcount : countTop (fun v => (ballots v).ranking) 2 = 6 := rfl
  have hcard : (votersTop profile (2 : Fin 3)).card = 6 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile'_0 : topCount profile' (0 : Fin 3) = 8 := by
  have hcount : countTop (fun v => (ballots' v).ranking) 0 = 8 := rfl
  have hcard : (votersTop profile' (0 : Fin 3)).card = 8 := by
    simpa [profile', votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile'_1 : topCount profile' (1 : Fin 3) = 5 := by
  have hcount : countTop (fun v => (ballots' v).ranking) 1 = 5 := rfl
  have hcard : (votersTop profile' (1 : Fin 3)).card = 5 := by
    simpa [profile', votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile'_2 : topCount profile' (2 : Fin 3) = 4 := by
  have hcount : countTop (fun v => (ballots' v).ranking) 2 = 4 := rfl
  have hcard : (votersTop profile' (2 : Fin 3)).card = 4 := by
    simpa [profile', votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma plurality_profile_has_0 :
    (0 : Fin 3) ∈ plurality profile := by
  classical
  have hmax : ∀ d : Fin 3, topCount profile d ≤ topCount profile 0 := by
    intro d
    fin_cases d <;> simp [topCount_profile_0, topCount_profile_1, topCount_profile_2]
  have hmem :
      (0 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3, topCount profile d ≤ topCount profile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_profile_has_2 :
    (2 : Fin 3) ∈ plurality profile := by
  classical
  have hmax : ∀ d : Fin 3, topCount profile d ≤ topCount profile 2 := by
    intro d
    fin_cases d <;> simp [topCount_profile_0, topCount_profile_1, topCount_profile_2]
  have hmem :
      (2 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3, topCount profile d ≤ topCount profile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_profile_not_1 :
    (1 : Fin 3) ∉ plurality profile := by
  classical
  intro h
  have hmax :
      ∀ d : Fin 3, topCount profile d ≤ topCount profile 1 := by
    simpa [plurality] using h
  have hlt : topCount profile 0 ≤ topCount profile 1 := hmax 0
  simp [topCount_profile_0, topCount_profile_1] at hlt

private lemma plurality_profile_eq : plurality profile = ({0, 2} : Finset (Fin 3)) := by
  classical
  apply Finset.ext
  intro x
  fin_cases x <;> simp [plurality_profile_has_0, plurality_profile_has_2, plurality_profile_not_1]

private lemma plurality_profile'_has_0 :
    (0 : Fin 3) ∈ plurality profile' := by
  classical
  have hmax : ∀ d : Fin 3, topCount profile' d ≤ topCount profile' 0 := by
    intro d
    fin_cases d <;> simp [topCount_profile'_0, topCount_profile'_1, topCount_profile'_2]
  have hmem :
      (0 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3, topCount profile' d ≤ topCount profile' c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_profile'_not_1 :
    (1 : Fin 3) ∉ plurality profile' := by
  classical
  intro h
  have hmax :
      ∀ d : Fin 3, topCount profile' d ≤ topCount profile' 1 := by
    simpa [plurality] using h
  have hlt : topCount profile' 0 ≤ topCount profile' 1 := hmax 0
  simp [topCount_profile'_0, topCount_profile'_1] at hlt

private lemma plurality_profile'_not_2 :
    (2 : Fin 3) ∉ plurality profile' := by
  classical
  intro h
  have hmax :
      ∀ d : Fin 3, topCount profile' d ≤ topCount profile' 2 := by
    simpa [plurality] using h
  have hlt : topCount profile' 0 ≤ topCount profile' 2 := hmax 0
  simp [topCount_profile'_0, topCount_profile'_2] at hlt

private lemma plurality_profile'_eq : plurality profile' = ({0} : Finset (Fin 3)) := by
  classical
  apply Finset.ext
  intro x
  fin_cases x <;> simp [plurality_profile'_has_0, plurality_profile'_not_1, plurality_profile'_not_2]

private lemma marginList_profile_0_2 :
    marginList (fun v => (ballots v).ranking) 0 2 = 5 := by
  rfl

private lemma marginList_profile'_0_1 :
    marginList (fun v => (ballots' v).ranking) 0 1 = -1 := by
  rfl

private lemma margin_profile_0_2 : margin profile (0 : Fin 3) (2 : Fin 3) = 5 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (0 : Fin 3)) (b := (2 : Fin 3))
  simpa [profile, marginList_profile_0_2] using h

private lemma margin_profile'_0_1 : margin profile' (0 : Fin 3) (1 : Fin 3) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (0 : Fin 3)) (b := (1 : Fin 3))
  simpa [profile', marginList_profile'_0_1] using h

private lemma pair_02_mem_pairs :
    ({0, 2} : Finset (Fin 3)) ∈
      pluralityWithRunoffPairs profile := by
  classical
  have hS : (plurality profile).card >= 2 := by
    simp [plurality_profile_eq]
  have hsubset : ({0, 2} : Finset (Fin 3)) ⊆ plurality profile := by
    intro x hx
    simpa [plurality_profile_eq] using hx
  have hcardpair : ({0, 2} : Finset (Fin 3)).card = 2 := by
    simp
  have hmem : ({0, 2} : Finset (Fin 3)) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma secondPluralitySet_profile' :
    secondPluralitySet profile' (plurality profile') = ({1} : Finset (Fin 3)) := by
  classical
  apply Finset.ext
  intro x
  fin_cases x
  · -- x = 0
    have hxS : (0 : Fin 3) ∈ plurality profile' := by
      simp [plurality_profile'_eq]
    have hx : (0 : Fin 3) ∉ secondPluralitySet profile' (plurality profile') := by
      intro hx'
      exact (mem_secondPluralitySet_not_mem (P := profile') (S := plurality profile') hx') hxS
    simp [hx]
  · -- x = 1
    have hR : (Finset.univ.filter (fun c => c ∉ plurality profile')).Nonempty := by
      refine ⟨1, ?_⟩
      simp [plurality_profile'_eq]
    have hx :
        (1 : Fin 3) ∈ secondPluralitySet profile' (plurality profile') := by
      refine (mem_secondPluralitySet_iff_forall_le (P := profile') (S := plurality profile') hR).2 ?_
      refine ⟨?_, ?_⟩
      · simp [plurality_profile'_eq]
      · intro e he
        fin_cases e <;>
          simp [plurality_profile'_eq, topCount_profile'_1, topCount_profile'_2] at he ⊢
    simp [hx]
  · -- x = 2
    have hR : (Finset.univ.filter (fun c => c ∉ plurality profile')).Nonempty := by
      refine ⟨1, ?_⟩
      simp [plurality_profile'_eq]
    have hx :
        (2 : Fin 3) ∈ secondPluralitySet profile' (plurality profile') -> False := by
      intro hx'
      have hx'' :=
        (mem_secondPluralitySet_iff_forall_le (P := profile') (S := plurality profile') hR).1 hx'
      rcases hx'' with ⟨hxR, hle⟩
      have hle' := hle 1 (by
        simp [plurality_profile'_eq])
      have hle'' := hle'
      simp [topCount_profile'_1, topCount_profile'_2] at hle''
    have hx' : (2 : Fin 3) ∉ secondPluralitySet profile' (plurality profile') := by
      intro hx''
      exact hx hx''
    simp [hx']

private lemma pluralityWithRunoffPairs_profile' :
    pluralityWithRunoffPairs profile' =
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  classical
  have hT :
      secondPluralitySet profile' ({0} : Finset (Fin 3)) = ({1} : Finset (Fin 3)) := by
    simpa [plurality_profile'_eq] using secondPluralitySet_profile'
  calc
    pluralityWithRunoffPairs profile' =
        (({0} : Finset (Fin 3)).product ({1} : Finset (Fin 3))).image
          (fun p => ({p.1, p.2} : Finset (Fin 3))) := by
        simp [pluralityWithRunoffPairs, plurality_profile'_eq, hT]
    _ = ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
        simp

private lemma mem_pluralityWithRunoff_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hcard : ¬ Fintype.card A <= 1) :
    x ∈ pluralityWithRunoff P ↔
      ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 <= margin P x y := by
  classical
  by_cases hcard' : Fintype.card A <= 1
  · exact (hcard hcard').elim
  · simp [pluralityWithRunoff, hcard']

private lemma pluralityWithRunoff_profile_has_0 :
    (0 : Fin 3) ∈ pluralityWithRunoff profile := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  have hmargin : 0 <= margin profile (0 : Fin 3) (2 : Fin 3) := by
    simp [margin_profile_0_2]
  have hpair_default : pairC 0 2 ∈ pluralityWithRunoffPairs profile := by
    simpa [pairC_eq_pair] using pair_02_mem_pairs
  have hpair_classical : pairC 0 2 ∈
      @pluralityWithRunoffPairs (Fin 17) (Fin 3) _ _ (Classical.decEq (Fin 3)) profile := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile)
          (inst1 := (inferInstance : DecidableEq (Fin 3)))
          (inst2 := Classical.decEq (Fin 3))
          (s := pairC 0 2)).1
        hpair_default
  have hpair_classical' := hpair_classical
  simp [pairC] at hpair_classical'
  exact (mem_pluralityWithRunoff_iff (P := profile) (x := (0 : Fin 3)) (hcard := hcard)).2
    ⟨(2 : Fin 3), hpair_classical', hmargin⟩

private lemma pluralityWithRunoff_profile'_not_0 :
    (0 : Fin 3) ∉ pluralityWithRunoff profile' := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  intro hmem
  rcases (mem_pluralityWithRunoff_iff (P := profile') (x := (0 : Fin 3)) (hcard := hcard)).1 hmem with
    ⟨y, hyPair, hmargin⟩
  have hyset : ({0, y} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
    have hyPair_classical : pairC 0 y ∈
        @pluralityWithRunoffPairs (Fin 17) (Fin 3) _ _ (Classical.decEq (Fin 3)) profile' := by
      simpa [pairC] using hyPair
    have hyPair_default : pairC 0 y ∈ pluralityWithRunoffPairs profile' := by
      exact
        (mem_pluralityWithRunoffPairs_decEq_congr (P := profile')
            (inst1 := Classical.decEq (Fin 3))
            (inst2 := (inferInstance : DecidableEq (Fin 3)))
            (s := pairC 0 y)).1
          hyPair_classical
    have hyPair' : ({0, y} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile' := by
      simpa [pairC_eq_pair] using hyPair_default
    simpa [pluralityWithRunoffPairs_profile'] using hyPair'
  have hy : y = (1 : Fin 3) := by
    have hmem : (1 : Fin 3) ∈ ({0, y} : Finset (Fin 3)) := by
      simp [hyset]
    have hmem' : (1 : Fin 3) = 0 ∨ (1 : Fin 3) = y := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    cases hmem' with
    | inl h =>
        exact (False.elim ((by simp : (1 : Fin 3) ≠ 0) h))
    | inr h =>
        simpa using h.symm
  subst hy
  have hmargin' : (0 : Int) <= -1 := by
    have hmargin' := hmargin
    simp [margin_profile'_0_1] at hmargin'
  exact (by decide : ¬ ((0 : Int) <= -1)) hmargin'

private lemma irv_profile_has_0 :
    (0 : Fin 3) ∈ instantRunoffVoting profile := by
  have hIRV :
      instantRunoffVoting profile = pluralityWithRunoff profile := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (V := Fin 17) (A := Fin 3) (hcard := by decide) (P := profile))
  simpa [hIRV] using pluralityWithRunoff_profile_has_0

private lemma irv_profile'_not_0 :
    (0 : Fin 3) ∉ instantRunoffVoting profile' := by
  have hIRV :
      instantRunoffVoting profile' = pluralityWithRunoff profile' := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (V := Fin 17) (A := Fin 3) (hcard := by decide) (P := profile'))
  simpa [hIRV] using pluralityWithRunoff_profile'_not_0

private lemma prefers_1_2_iff (v : Fin 17) :
    Prefers profile v (1 : Fin 3) (2 : Fin 3) ↔
      Prefers profile' v (1 : Fin 3) (2 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma prefers_2_1_iff (v : Fin 17) :
    Prefers profile v (2 : Fin 3) (1 : Fin 3) ↔
      Prefers profile' v (2 : Fin 3) (1 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma simpleLift_profile : simpleLift profile' profile (0 : Fin 3) := by
  classical
  constructor
  · intro v a b ha hb
    have ha' : a = (1 : Fin 3) ∨ a = (2 : Fin 3) := by
      fin_cases a
      · cases ha rfl
      · simp
      · simp
    have hb' : b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
      fin_cases b
      · cases hb rfl
      · simp
      · simp
    rcases ha' with rfl | rfl
    · rcases hb' with rfl | rfl
      · simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList]
      · simpa using prefers_1_2_iff v
    · rcases hb' with rfl | rfl
      · simpa using prefers_2_1_iff v
      · simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList]
  · intro a v
    constructor
    · fin_cases a <;> fin_cases v <;>
        simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
        decide
    · fin_cases a <;> fin_cases v <;>
        simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
        decide

theorem instantRunoffVoting_not_monotonicity : ¬ Monotonicity instantRunoffVoting := by
  intro hmono
  have hx : (0 : Fin 3) ∈ instantRunoffVoting profile := irv_profile_has_0
  have hlift : simpleLift profile' profile (0 : Fin 3) := simpleLift_profile
  have hx' : (0 : Fin 3) ∈ instantRunoffVoting profile' := hmono profile profile' 0 hx hlift
  exact irv_profile'_not_0 hx'

theorem pluralityWithRunoff_not_monotonicity : ¬ Monotonicity pluralityWithRunoff := by
  intro hmono
  have hx : (0 : Fin 3) ∈ pluralityWithRunoff profile := pluralityWithRunoff_profile_has_0
  have hlift : simpleLift profile' profile (0 : Fin 3) := simpleLift_profile
  have hx' : (0 : Fin 3) ∈ pluralityWithRunoff profile' := hmono profile profile' 0 hx hlift
  exact pluralityWithRunoff_profile'_not_0 hx'

end PluralityWithRunoffMonotonicityCounterexample

end SocialChoice
