import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Majority
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset
open Classical

/-!
# Plurality with Runoff fails the mutual majority criterion

We use a five-voter profile with five candidates. The strict majority
{0,1,2} ranks every candidate in {0,1,2} above {3,4}, but candidate 3
can win a runoff against 4.
-/

namespace PluralityWithRunoffMutualMajorityCounterexample

def ballot01234 : ListBallot 5 := ListBallot.mk' [0, 1, 2, 3, 4]
def ballot12034 : ListBallot 5 := ListBallot.mk' [1, 2, 0, 3, 4]
def ballot20134 : ListBallot 5 := ListBallot.mk' [2, 0, 1, 3, 4]
def ballot34012 : ListBallot 5 := ListBallot.mk' [3, 4, 0, 1, 2]
def ballot43012 : ListBallot 5 := ListBallot.mk' [4, 3, 0, 1, 2]

def ballots : Fin 5 → ListBallot 5
  | 0 => ballot01234
  | 1 => ballot12034
  | 2 => ballot20134
  | 3 => ballot34012
  | 4 => ballot43012
  | _ => ballot01234

noncomputable def profile : Profile (Fin 5) (Fin 5) :=
  profileOfListBallots ballots

private lemma topCount_profile_0 : topCount profile (0 : Fin 5) = 1 := by
  have hcount : countTop (fun v => (ballots v).ranking) 0 = 1 := rfl
  have hcard : (votersTop profile (0 : Fin 5)).card = 1 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_1 : topCount profile (1 : Fin 5) = 1 := by
  have hcount : countTop (fun v => (ballots v).ranking) 1 = 1 := rfl
  have hcard : (votersTop profile (1 : Fin 5)).card = 1 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_2 : topCount profile (2 : Fin 5) = 1 := by
  have hcount : countTop (fun v => (ballots v).ranking) 2 = 1 := rfl
  have hcard : (votersTop profile (2 : Fin 5)).card = 1 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_3 : topCount profile (3 : Fin 5) = 1 := by
  have hcount : countTop (fun v => (ballots v).ranking) 3 = 1 := rfl
  have hcard : (votersTop profile (3 : Fin 5)).card = 1 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_4 : topCount profile (4 : Fin 5) = 1 := by
  have hcount : countTop (fun v => (ballots v).ranking) 4 = 1 := rfl
  have hcard : (votersTop profile (4 : Fin 5)).card = 1 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_eq_one (c : Fin 5) : topCount profile c = 1 := by
  fin_cases c <;> simp [topCount_profile_0, topCount_profile_1, topCount_profile_2,
    topCount_profile_3, topCount_profile_4]

private noncomputable def pairC (x y : Fin 5) : Finset (Fin 5) := by
  letI : DecidableEq (Fin 5) := Classical.decEq (Fin 5)
  exact insert x ({y} : Finset (Fin 5))

private lemma pairC_eq_pair (x y : Fin 5) : pairC x y = ({x, y} : Finset (Fin 5)) := by
  classical
  ext z
  simp [pairC, Finset.mem_insert, Finset.mem_singleton]

private lemma plurality_profile_eq :
    plurality profile = (Finset.univ : Finset (Fin 5)) := by
  letI : DecidableEq (Fin 5) := instDecidableEqFin 5
  apply Finset.ext
  intro c
  constructor
  · intro _hc
    exact mem_univ c
  · intro _hc
    have hmax : ∀ d : Fin 5, topCount profile d ≤ topCount profile c := by
      intro d
      simp [topCount_profile_eq_one d, topCount_profile_eq_one c]
    have hmem :
        c ∈ (Finset.univ.filter (fun c : Fin 5 =>
          ∀ d : Fin 5, topCount profile d ≤ topCount profile c)) := by
      exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
    simpa [plurality] using hmem

private lemma pair_34_mem_pairs :
    ({3, 4} : Finset (Fin 5)) ∈ pluralityWithRunoffPairs profile := by
  classical
  have hS : (plurality profile).card ≥ 2 := by
    simp [plurality_profile_eq]
  have hsubset : ({3, 4} : Finset (Fin 5)) ⊆ plurality profile := by
    intro x hx
    simp [plurality_profile_eq]
  have hcardpair : ({3, 4} : Finset (Fin 5)).card = 2 := by
    simp
  have hmem : ({3, 4} : Finset (Fin 5)) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma marginList_profile_3_4 :
    marginList (fun v => (ballots v).ranking) 3 4 = 3 := by
  rfl

private lemma margin_profile_3_4 : margin profile (3 : Fin 5) (4 : Fin 5) = 3 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (3 : Fin 5)) (b := (4 : Fin 5))
  simpa [profile, marginList_profile_3_4] using h

private lemma mem_pluralityWithRunoff_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hcard : ¬ Fintype.card A <= 1) :
    x ∈ pluralityWithRunoff P ↔
      ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P x y := by
  classical
  by_cases hcard' : Fintype.card A <= 1
  · exact (hcard hcard').elim
  · simp [pluralityWithRunoff, hcard']

private lemma pluralityWithRunoff_profile_has_3 :
    (3 : Fin 5) ∈ pluralityWithRunoff profile := by
  classical
  have hcard : ¬ Fintype.card (Fin 5) <= 1 := by decide
  have hmargin : 0 ≤ margin profile (3 : Fin 5) (4 : Fin 5) := by
    simp [margin_profile_3_4]
  have hpair_default : ({3, 4} : Finset (Fin 5)) ∈ pluralityWithRunoffPairs profile :=
    pair_34_mem_pairs
  have hpair_classical : pairC 3 4 ∈
      @pluralityWithRunoffPairs (Fin 5) (Fin 5) _ _ (Classical.decEq (Fin 5)) profile := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile)
          (inst1 := (inferInstance : DecidableEq (Fin 5)))
          (inst2 := Classical.decEq (Fin 5))
          (s := pairC 3 4)).1
        (by simpa [pairC_eq_pair] using hpair_default)
  have hpair_classical' := hpair_classical
  simp [pairC] at hpair_classical'
  exact (mem_pluralityWithRunoff_iff (P := profile) (x := (3 : Fin 5)) (hcard := hcard)).2
    ⟨(4 : Fin 5), hpair_classical', hmargin⟩

private def S : Finset (Fin 5) := {0, 1, 2}
private def T : Finset (Fin 5) := {0, 1, 2}

private lemma strictMajority_S : StrictMajority S := by
  unfold StrictMajority S
  simp

private lemma T_nonempty : T.Nonempty := by
  simp [T]

private lemma prefers_T_over_Tc :
    ∀ v ∈ S, ∀ a ∈ T, ∀ b ∉ T, Prefers profile v a b := by
  intro v hv a ha b hb
  fin_cases v
  · -- v = 0
    fin_cases a <;> fin_cases b <;>
      (simp [profile, ballots, prefers_iff_prefersInList, prefersInList, T] at ha hb ⊢
        <;> cases ha <;> cases hb <;> decide)
  · -- v = 1
    fin_cases a <;> fin_cases b <;>
      (simp [profile, ballots, prefers_iff_prefersInList, prefersInList, T] at ha hb ⊢
        <;> cases ha <;> cases hb <;> decide)
  · -- v = 2
    fin_cases a <;> fin_cases b <;>
      (simp [profile, ballots, prefers_iff_prefersInList, prefersInList, T] at ha hb ⊢
        <;> cases ha <;> cases hb <;> decide)
  · -- v = 3
    have : False := by
      simp [S] at hv
    exact this.elim
  · -- v = 4
    have : False := by
      simp [S] at hv
    exact this.elim

theorem pluralityWithRunoff_not_mutualMajorityCriterion :
    ¬ MutualMajorityCriterion pluralityWithRunoff := by
  intro hmut
  have hsubset :
      pluralityWithRunoff profile ⊆ T :=
    hmut (P := profile) (S := S) (T := T) strictMajority_S T_nonempty prefers_T_over_Tc
  have hwin : (3 : Fin 5) ∈ pluralityWithRunoff profile :=
    pluralityWithRunoff_profile_has_3
  have hnot : (3 : Fin 5) ∉ T := by
    simp [T]
  exact hnot (hsubset hwin)

end PluralityWithRunoffMutualMajorityCounterexample

end SocialChoice
