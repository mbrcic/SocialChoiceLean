import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Margin

namespace SocialChoice

open Finset

lemma dominatesSet_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (S : Finset A) :
    dominatesSet P S → dominatesSet (permuteCandidates P σ) (permuteWinners σ S) := by
  classical
  intro hS
  rcases hS with ⟨hS_nonempty, hS_dom⟩
  refine ⟨?_, ?_⟩
  · rcases hS_nonempty with ⟨a, ha⟩
    refine ⟨σ a, ?_⟩
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
  · intro a ha b hb
    rcases Finset.mem_map.mp ha with ⟨a0, ha0, rfl⟩
    have hb' : σ.symm b ∉ S := by
      intro hbS
      apply hb
      exact Finset.mem_map.mpr ⟨σ.symm b, hbS, by simp⟩
    have hpos : margin_pos P a0 (σ.symm b) := hS_dom a0 ha0 (σ.symm b) hb'
    exact
      (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := σ a0) (b := b)).2
        (by simpa using hpos)

lemma dominatesSet_permuteCandidates_symm {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (S : Finset A) :
    dominatesSet (permuteCandidates P σ) S → dominatesSet P (permuteWinners σ.symm S) := by
  classical
  intro hS
  rcases hS with ⟨hS_nonempty, hS_dom⟩
  refine ⟨?_, ?_⟩
  · rcases hS_nonempty with ⟨a, ha⟩
    refine ⟨σ.symm a, ?_⟩
    exact Finset.mem_map.mpr ⟨a, ha, by simp⟩
  · intro a ha b hb
    rcases Finset.mem_map.mp ha with ⟨a0, ha0, haEq⟩
    have hb' : σ b ∉ S := by
      intro hbS
      apply hb
      exact Finset.mem_map.mpr ⟨σ b, hbS, by simp⟩
    have hpos : margin_pos (permuteCandidates P σ) a0 (σ b) := hS_dom a0 ha0 (σ b) hb'
    have hpos' : margin_pos P (σ.symm a0) b := by
      simpa using
        (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := a0) (b := σ b)).1 hpos
    cases haEq
    simpa using hpos'

lemma topCycleSet_permuteCandidates {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (σ : Equiv.Perm A) :
    topCycleSet (P := permuteCandidates P σ) =
      permuteWinners σ (topCycleSet (P := P)) := by
  classical
  have hdomS : dominatesSet P (topCycleSet (P := P)) := topCycleSet_dominates (P := P)
  have hdomS' :
      dominatesSet (permuteCandidates P σ) (permuteWinners σ (topCycleSet (P := P))) :=
    dominatesSet_permuteCandidates (P := P) (σ := σ) (S := topCycleSet (P := P)) hdomS
  have hsubset₁ :
      topCycleSet (P := permuteCandidates P σ) ⊆
        permuteWinners σ (topCycleSet (P := P)) :=
    topCycleSet_subset_of_dominates (P := permuteCandidates P σ)
      (S := permuteWinners σ (topCycleSet (P := P))) hdomS'
  have hdomT :
      dominatesSet (permuteCandidates P σ) (topCycleSet (P := permuteCandidates P σ)) :=
    topCycleSet_dominates (P := permuteCandidates P σ)
  have hdomT' :
      dominatesSet P (permuteWinners σ.symm (topCycleSet (P := permuteCandidates P σ))) :=
    dominatesSet_permuteCandidates_symm (P := P) (σ := σ)
      (S := topCycleSet (P := permuteCandidates P σ)) hdomT
  have hsubset₂' :
      topCycleSet (P := P) ⊆
        permuteWinners σ.symm (topCycleSet (P := permuteCandidates P σ)) :=
    topCycleSet_subset_of_dominates (P := P)
      (S := permuteWinners σ.symm (topCycleSet (P := permuteCandidates P σ))) hdomT'
  have hsubset₂ :
      permuteWinners σ (topCycleSet (P := P)) ⊆
        topCycleSet (P := permuteCandidates P σ) := by
    intro c hc
    rcases Finset.mem_map.mp hc with ⟨a, ha, rfl⟩
    have ha' :
        a ∈ permuteWinners σ.symm (topCycleSet (P := permuteCandidates P σ)) :=
      hsubset₂' ha
    rcases Finset.mem_map.mp ha' with ⟨b, hb, hbEq⟩
    have hbEq' : b = σ a := by
      have := congrArg (fun x => σ x) hbEq
      simpa using this
    simpa [hbEq'] using hb
  apply Finset.ext
  intro a
  constructor
  · intro ha
    exact hsubset₁ ha
  · intro ha
    exact hsubset₂ ha

theorem topCycle_neutral : Neutrality topCycle := by
  intro V A _ _ P σ
  classical
  by_cases hA : Nonempty A
  ·
    let _ : Nonempty A := hA
    have hset :
        topCycleSet (P := permuteCandidates P σ) =
          permuteWinners σ (topCycleSet (P := P)) :=
      topCycleSet_permuteCandidates (P := P) (σ := σ)
    simp [topCycle, hA, hset]
  ·
    simp [topCycle, hA, permuteWinners]

end SocialChoice
