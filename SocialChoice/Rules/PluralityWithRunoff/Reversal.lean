import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset
open Classical

namespace PluralityWithRunoffReversalCounterexample

def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotBCA
  | ⟨1, _⟩ => ballotBCA
  | ⟨2, _⟩ => ballotCAB
  | ⟨3, _⟩ => ballotABC
  | ⟨4, _⟩ => ballotABC

noncomputable def profile : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots ballots

private noncomputable def pairC (x y : Fin 3) : Finset (Fin 3) := by
  classical
  letI : DecidableEq (Fin 3) := Classical.decEq (Fin 3)
  exact insert x ({y} : Finset (Fin 3))

private lemma pairC_eq_pair (x y : Fin 3) : pairC x y = ({x, y} : Finset (Fin 3)) := by
  classical
  ext z
  simp [pairC, Finset.mem_insert, Finset.mem_singleton]

private lemma mem_pluralityWithRunoff_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hcard : ¬ Fintype.card A ≤ 1) :
    x ∈ pluralityWithRunoff P ↔
      ∃ y : A,
        ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P x y := by
  classical
  by_cases hcard' : Fintype.card A ≤ 1
  · exact (hcard hcard').elim
  · simp [pluralityWithRunoff, hcard']

private lemma bottomRank_iff_prefersInList {m n : ℕ} (ballots : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (ballots v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).2 (h d hd)

private lemma topRank_reverse_profile_iff_bottomRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) :
    TopRank (reverse_profile P) v c ↔ BottomRank P v c := by
  constructor
  · intro h d hd
    simpa using (h d hd)
  · intro h d hd
    simpa using (h d hd)

private lemma votersBottom_profile_0 :
    votersBottom profile (0 : Fin 3) = ({0, 1} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_1 :
    votersBottom profile (1 : Fin 3) = ({2} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_2 :
    votersBottom profile (2 : Fin 3) = ({3, 4} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma topCount_profile_0 : topCount profile (0 : Fin 3) = 2 := by
  calc
    topCount profile (0 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 0 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (0 : Fin 3)))
    _ = 2 := rfl

private lemma topCount_profile_1 : topCount profile (1 : Fin 3) = 2 := by
  calc
    topCount profile (1 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 1 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (1 : Fin 3)))
    _ = 2 := rfl

private lemma topCount_profile_2 : topCount profile (2 : Fin 3) = 1 := by
  calc
    topCount profile (2 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 2 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (2 : Fin 3)))
    _ = 1 := rfl

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

private lemma plurality_profile_has_1 :
    (1 : Fin 3) ∈ plurality profile := by
  classical
  have hmax : ∀ d : Fin 3, topCount profile d ≤ topCount profile 1 := by
    intro d
    fin_cases d <;> simp [topCount_profile_0, topCount_profile_1, topCount_profile_2]
  have hmem :
      (1 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3, topCount profile d ≤ topCount profile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_profile_not_2 :
    (2 : Fin 3) ∉ plurality profile := by
  intro h
  have hmax : ∀ d : Fin 3, topCount profile d ≤ topCount profile (2 : Fin 3) := by
    have hmem :
        (2 : Fin 3) ∈
          (Finset.univ.filter (fun c : Fin 3 =>
            ∀ d : Fin 3, topCount profile d ≤ topCount profile c)) := by
      simpa [plurality] using h
    exact (Finset.mem_filter.mp hmem).2
  have h0le : topCount profile 0 ≤ topCount profile (2 : Fin 3) := hmax 0
  have h0le' : (2 : Nat) ≤ 1 := by
    have h0le' := h0le
    simp [topCount_profile_0, topCount_profile_2] at h0le'
  exact (by decide : ¬ ((2 : Nat) ≤ 1)) h0le'

private lemma plurality_profile_eq : plurality profile = ({0, 1} : Finset (Fin 3)) := by
  classical
  ext x
  fin_cases x
  · simpa using plurality_profile_has_0
  · simpa using plurality_profile_has_1
  · constructor
    · intro hx
      exfalso
      exact plurality_profile_not_2 hx
    · intro hx
      have hne : (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)) := by decide
      exact (hne hx).elim

private lemma marginList_profile_0_1 :
    marginList (fun v => (ballots v).ranking) 0 1 = 1 := by
  rfl

private lemma marginList_profile_1_0 :
    marginList (fun v => (ballots v).ranking) 1 0 = -1 := by
  rfl

private lemma marginList_profile_2_0 :
    marginList (fun v => (ballots v).ranking) 2 0 = 1 := by
  rfl

private lemma margin_profile_0_1 : margin profile (0 : Fin 3) (1 : Fin 3) = 1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (0 : Fin 3)) (b := (1 : Fin 3))
  simpa [profile, marginList_profile_0_1] using h

private lemma margin_profile_1_0 : margin profile (1 : Fin 3) (0 : Fin 3) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (1 : Fin 3)) (b := (0 : Fin 3))
  simpa [profile, marginList_profile_1_0] using h

private lemma margin_profile_2_0 : margin profile (2 : Fin 3) (0 : Fin 3) = 1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (2 : Fin 3)) (b := (0 : Fin 3))
  simpa [profile, marginList_profile_2_0] using h

private lemma pair_01_mem_pairs :
    ({0, 1} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
  classical
  have hS : (plurality profile).card ≥ 2 := by
    simp [plurality_profile_eq]
  have hsubset : ({0, 1} : Finset (Fin 3)) ⊆ plurality profile := by
    intro x hx
    simpa [plurality_profile_eq] using hx
  have hcardpair : ({0, 1} : Finset (Fin 3)).card = 2 := by
    simp
  have hmem :
      ({0, 1} : Finset (Fin 3)) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma pluralityWithRunoff_profile_has_0 :
    (0 : Fin 3) ∈ pluralityWithRunoff profile := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have hmargin : 0 ≤ margin profile (0 : Fin 3) (1 : Fin 3) := by
    simp [margin_profile_0_1]
  have hpair_default : pairC 0 1 ∈ pluralityWithRunoffPairs profile := by
    simpa [pairC_eq_pair] using pair_01_mem_pairs
  have hpair_classical : pairC 0 1 ∈
      @pluralityWithRunoffPairs (Fin 5) (Fin 3) _ _ (Classical.decEq (Fin 3)) profile := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile)
          (inst1 := (inferInstance : DecidableEq (Fin 3)))
          (inst2 := Classical.decEq (Fin 3))
          (s := pairC 0 1)).1
        hpair_default
  exact (mem_pluralityWithRunoff_iff (P := profile) (x := (0 : Fin 3)) (hcard := hcard)).2
    ⟨(1 : Fin 3), by simpa [pairC] using hpair_classical, hmargin⟩

private lemma pluralityWithRunoffPairs_profile :
    pluralityWithRunoffPairs profile =
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  classical
  ext s
  constructor
  · intro hs
    have hs' : s ∈ (plurality profile).powersetCard 2 := by
      have hS : (plurality profile).card ≥ 2 := by
        simp [plurality_profile_eq]
      simpa [pluralityWithRunoffPairs, hS] using hs
    rcases Finset.mem_powersetCard.mp hs' with ⟨hsS, hcard⟩
    have hsS' : s ⊆ ({0, 1} : Finset (Fin 3)) := by
      simpa [plurality_profile_eq] using hsS
    have hcardpair : ({0, 1} : Finset (Fin 3)).card = 2 := by
      simp
    have hcard_le : ({0, 1} : Finset (Fin 3)).card ≤ s.card := by
      simp [hcardpair, hcard]
    have hEq : s = ({0, 1} : Finset (Fin 3)) :=
      Finset.eq_of_subset_of_card_le hsS' hcard_le
    simp [hEq]
  · intro hs
    have hs' : s = ({0, 1} : Finset (Fin 3)) := by
      simpa [Finset.mem_singleton] using hs
    subst hs'
    simpa using pair_01_mem_pairs

private lemma pluralityWithRunoff_profile_not_1 :
    (1 : Fin 3) ∉ pluralityWithRunoff profile := by
  classical
  intro h
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have h' :=
    (mem_pluralityWithRunoff_iff (P := profile) (x := (1 : Fin 3)) (hcard := hcard)).1 h
  rcases h' with ⟨y, hyPair, hyMargin⟩
  have hyPair_classical :
      pairC 1 y ∈
        @pluralityWithRunoffPairs (Fin 5) (Fin 3) _ _ (Classical.decEq (Fin 3)) profile := by
    simpa [pairC] using hyPair
  have hyPair_default : pairC 1 y ∈ pluralityWithRunoffPairs profile := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile)
          (inst1 := Classical.decEq (Fin 3))
          (inst2 := (inferInstance : DecidableEq (Fin 3)))
          (s := pairC 1 y)).1
        hyPair_classical
  have hyPair' :
      ({1, y} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
    simpa [pairC_eq_pair] using hyPair_default
  fin_cases y
  · simp [margin_profile_1_0] at hyMargin
  · have hmem : ({1, 1} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
      simpa using hyPair'
    have hEq : ({1, 1} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile] using hmem
    have hne : ({1, 1} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3)) := by
      decide
    exact hne hEq
  · have hmem : ({1, 2} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
      simpa using hyPair'
    have hEq : ({1, 2} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile] using hmem
    have hne : ({1, 2} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3)) := by
      decide
    exact hne hEq

private lemma pluralityWithRunoff_profile_not_2 :
    (2 : Fin 3) ∉ pluralityWithRunoff profile := by
  classical
  intro h
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have h' :=
    (mem_pluralityWithRunoff_iff (P := profile) (x := (2 : Fin 3)) (hcard := hcard)).1 h
  rcases h' with ⟨y, hyPair, _hyMargin⟩
  have hyPair_classical :
      pairC 2 y ∈
        @pluralityWithRunoffPairs (Fin 5) (Fin 3) _ _ (Classical.decEq (Fin 3)) profile := by
    simpa [pairC] using hyPair
  have hyPair_default : pairC 2 y ∈ pluralityWithRunoffPairs profile := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile)
          (inst1 := Classical.decEq (Fin 3))
          (inst2 := (inferInstance : DecidableEq (Fin 3)))
          (s := pairC 2 y)).1
        hyPair_classical
  have hyPair' :
      ({2, y} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
    simpa [pairC_eq_pair] using hyPair_default
  fin_cases y
  · have hmem : ({2, 0} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
      simpa using hyPair'
    have hEq : ({2, 0} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile] using hmem
    have hne : ({2, 0} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3)) := by
      decide
    exact hne hEq
  · have hmem : ({2, 1} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
      simpa using hyPair'
    have hEq : ({2, 1} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile] using hmem
    have hne : ({2, 1} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3)) := by
      decide
    exact hne hEq
  · have hmem : ({2, 2} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
      simpa using hyPair'
    have hEq : ({2, 2} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile] using hmem
    have hne : ({2, 2} : Finset (Fin 3)) ≠ ({0, 1} : Finset (Fin 3)) := by
      decide
    exact hne hEq

lemma pluralityWithRunoff_profile_eq_singleton : pluralityWithRunoff profile = {0} := by
  classical
  refine (Finset.eq_singleton_iff_unique_mem).2 ?_
  refine ⟨pluralityWithRunoff_profile_has_0, ?_⟩
  intro x hx
  fin_cases x
  · rfl
  · exfalso
    exact pluralityWithRunoff_profile_not_1 hx
  · exfalso
    exact pluralityWithRunoff_profile_not_2 hx

private lemma votersTop_reverse_profile_eq_votersBottom {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    votersTop (reverse_profile P) c = votersBottom P c := by
  classical
  ext v
  simp [votersTop, votersBottom, topRank_reverse_profile_iff_bottomRank]

private lemma topCount_reverse_profile_0 :
    topCount (reverse_profile profile) (0 : Fin 3) = 2 := by
  classical
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_0]

private lemma topCount_reverse_profile_1 :
    topCount (reverse_profile profile) (1 : Fin 3) = 1 := by
  classical
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_1]

private lemma topCount_reverse_profile_2 :
    topCount (reverse_profile profile) (2 : Fin 3) = 2 := by
  classical
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_2]

private lemma plurality_reverse_profile_has_0 :
    (0 : Fin 3) ∈ plurality (reverse_profile profile) := by
  classical
  have hmax :
      ∀ d : Fin 3,
        topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) 0 := by
    intro d
    fin_cases d <;>
      simp [topCount_reverse_profile_0, topCount_reverse_profile_1, topCount_reverse_profile_2]
  have hmem :
      (0 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3,
            topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_reverse_profile_has_2 :
    (2 : Fin 3) ∈ plurality (reverse_profile profile) := by
  classical
  have hmax :
      ∀ d : Fin 3,
        topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) 2 := by
    intro d
    fin_cases d <;>
      simp [topCount_reverse_profile_0, topCount_reverse_profile_1, topCount_reverse_profile_2]
  have hmem :
      (2 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3,
            topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma pair_02_mem_pairs_reverse :
    ({0, 2} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs (reverse_profile profile) := by
  classical
  have hmem0 : (0 : Fin 3) ∈ plurality (reverse_profile profile) :=
    plurality_reverse_profile_has_0
  have hmem2 : (2 : Fin 3) ∈ plurality (reverse_profile profile) :=
    plurality_reverse_profile_has_2
  have hS : (plurality (reverse_profile profile)).card ≥ 2 := by
    have hlt :
        1 < (plurality (reverse_profile profile)).card := by
      exact Finset.one_lt_card.mpr ⟨0, hmem0, 2, hmem2, by decide⟩
    exact (Nat.succ_le_iff.mp hlt)
  have hsubset : ({0, 2} : Finset (Fin 3)) ⊆ plurality (reverse_profile profile) := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcardpair : ({0, 2} : Finset (Fin 3)).card = 2 := by
    simp
  have hmem :
      ({0, 2} : Finset (Fin 3)) ∈ (plurality (reverse_profile profile)).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

lemma reverse_profile_has_0 :
    (0 : Fin 3) ∈ pluralityWithRunoff (reverse_profile profile) := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have hmargin :
      0 ≤ margin (reverse_profile profile) (0 : Fin 3) (2 : Fin 3) := by
    have h :=
      margin_reverse_eq (P := profile) (a := (2 : Fin 3)) (b := (0 : Fin 3))
    have h' : margin (reverse_profile profile) (0 : Fin 3) (2 : Fin 3) = 1 := by
      simpa [margin_profile_2_0] using h
    simp [h']
  have hpair_default : pairC 0 2 ∈ pluralityWithRunoffPairs (reverse_profile profile) := by
    simpa [pairC_eq_pair] using pair_02_mem_pairs_reverse
  have hpair_classical : pairC 0 2 ∈
      @pluralityWithRunoffPairs (Fin 5) (Fin 3) _ _ (Classical.decEq (Fin 3))
        (reverse_profile profile) := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := reverse_profile profile)
          (inst1 := (inferInstance : DecidableEq (Fin 3)))
          (inst2 := Classical.decEq (Fin 3))
          (s := pairC 0 2)).1
        hpair_default
  exact (mem_pluralityWithRunoff_iff (P := reverse_profile profile) (x := (0 : Fin 3))
    (hcard := hcard)).2 ⟨(2 : Fin 3), by simpa [pairC] using hpair_classical, hmargin⟩

end PluralityWithRunoffReversalCounterexample

theorem pluralityWithRunoff_not_singletonReversalSymmetry :
    ¬ SingletonReversalSymmetry pluralityWithRunoff := by
  intro h
  have hsingle :
      pluralityWithRunoff PluralityWithRunoffReversalCounterexample.profile = {0} :=
    PluralityWithRunoffReversalCounterexample.pluralityWithRunoff_profile_eq_singleton
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hnot :=
    h (P := PluralityWithRunoffReversalCounterexample.profile) (x := (0 : Fin 3)) hne hsingle
  have hw :
      (0 : Fin 3) ∈
        pluralityWithRunoff (reverse_profile PluralityWithRunoffReversalCounterexample.profile) :=
    PluralityWithRunoffReversalCounterexample.reverse_profile_has_0
  exact hnot hw

end SocialChoice
