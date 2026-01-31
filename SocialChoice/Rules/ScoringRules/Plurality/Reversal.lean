import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset
open Classical

namespace PluralityReversalCounterexample

def ballotCBA : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotACB : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 4 → ListBallot 3
  | 0 => ballotCBA
  | 1 => ballotBCA
  | 2 => ballotACB
  | 3 => ballotABC

noncomputable def profile : Profile (Fin 4) (Fin 3) :=
  profileOfListBallots ballots

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
    votersBottom profile (0 : Fin 3) = ({0, 1} : Finset (Fin 4)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_1 :
    votersBottom profile (1 : Fin 3) = ({2} : Finset (Fin 4)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_2 :
    votersBottom profile (2 : Fin 3) = ({3} : Finset (Fin 4)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_0_card :
    (votersBottom profile (0 : Fin 3)).card = 2 := by
  simp [votersBottom_profile_0]

private lemma votersBottom_profile_1_card :
    (votersBottom profile (1 : Fin 3)).card = 1 := by
  simp [votersBottom_profile_1]

private lemma votersBottom_profile_2_card :
    (votersBottom profile (2 : Fin 3)).card = 1 := by
  simp [votersBottom_profile_2]

private lemma topCount_profile_0 : topCount profile (0 : Fin 3) = 2 := by
  calc
    topCount profile (0 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 0 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (0 : Fin 3)))
    _ = 2 := rfl

private lemma topCount_profile_1 : topCount profile (1 : Fin 3) = 1 := by
  calc
    topCount profile (1 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 1 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (1 : Fin 3)))
    _ = 1 := rfl

private lemma topCount_profile_2 : topCount profile (2 : Fin 3) = 1 := by
  calc
    topCount profile (2 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 2 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (2 : Fin 3)))
    _ = 1 := rfl

private lemma topCount_profile_le (d : Fin 3) :
    topCount profile d ≤ topCount profile 0 := by
  fin_cases d <;>
    simp [topCount_profile_0, topCount_profile_1, topCount_profile_2]

private lemma plurality_profile_has_0 :
    (0 : Fin 3) ∈ plurality profile := by
  classical
  have hmax : ∀ d : Fin 3, topCount profile d ≤ topCount profile 0 := by
    intro d
    exact topCount_profile_le d
  have hmem :
      (0 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3, topCount profile d ≤ topCount profile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_profile_not_1 :
    (1 : Fin 3) ∉ plurality profile := by
  intro h
  have hmax : ∀ d : Fin 3, topCount profile d ≤ topCount profile (1 : Fin 3) := by
    have hmem :
        (1 : Fin 3) ∈
          (Finset.univ.filter (fun c : Fin 3 =>
            ∀ d : Fin 3, topCount profile d ≤ topCount profile c)) := by
      simpa [plurality] using h
    exact (Finset.mem_filter.mp hmem).2
  have h0le : topCount profile 0 ≤ topCount profile (1 : Fin 3) := hmax 0
  have h0le' : (2 : Nat) ≤ 1 := by
    have h0le' := h0le
    simp [topCount_profile_0, topCount_profile_1] at h0le'
  exact (by decide : ¬ ((2 : Nat) ≤ 1)) h0le'

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

lemma plurality_profile_eq_singleton : plurality profile = {0} := by
  classical
  refine (Finset.eq_singleton_iff_unique_mem).2 ?_
  refine ⟨plurality_profile_has_0, ?_⟩
  intro x hx
  fin_cases x
  · rfl
  · exfalso
    exact plurality_profile_not_1 hx
  · exfalso
    exact plurality_profile_not_2 hx

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
    topCount (reverse_profile profile) (2 : Fin 3) = 1 := by
  classical
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_2]

lemma reverse_profile_has_0 :
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

end PluralityReversalCounterexample

theorem plurality_not_singletonReversalSymmetry : ¬ SingletonReversalSymmetry plurality := by
  intro h
  have hsingle : plurality PluralityReversalCounterexample.profile = {0} :=
    PluralityReversalCounterexample.plurality_profile_eq_singleton
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hnot :=
    h (P := PluralityReversalCounterexample.profile) (x := (0 : Fin 3)) hne hsingle
  have hw : (0 : Fin 3) ∈ plurality (reverse_profile PluralityReversalCounterexample.profile) :=
    PluralityReversalCounterexample.reverse_profile_has_0
  exact hnot hw

end SocialChoice
