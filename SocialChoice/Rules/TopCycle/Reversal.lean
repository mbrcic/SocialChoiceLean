import SocialChoice.Axioms.Reversal
import SocialChoice.Margin
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

theorem topCycle_reversal_symmetry : ReversalSymmetry topCycle := by
  intro V A _ _ _ P hnot
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    have hset_ne_univ : topCycleSet (P := P) ≠ (Finset.univ : Finset A) := by
      simpa [topCycle, hA] using hnot
    have hcomp_nonempty :
        ((Finset.univ : Finset A) \ topCycleSet (P := P)).Nonempty := by
      by_contra hcomp
      have hcomp_eq_empty :
          ((Finset.univ : Finset A) \ topCycleSet (P := P)) = (∅ : Finset A) :=
        Finset.not_nonempty_iff_eq_empty.mp hcomp
      have huniv_subset : (Finset.univ : Finset A) ⊆ topCycleSet (P := P) :=
        (Finset.sdiff_eq_empty_iff_subset).mp hcomp_eq_empty
      have hset_eq_univ : topCycleSet (P := P) = (Finset.univ : Finset A) := by
        exact Finset.eq_univ_iff_forall.mpr (fun a => huniv_subset (by simp))
      exact hset_ne_univ hset_eq_univ
    have hcomp_dominates :
        dominatesSet (reverse_profile P) ((Finset.univ : Finset A) \ topCycleSet (P := P)) := by
      refine ⟨hcomp_nonempty, ?_⟩
      intro a ha b hb
      have ha_not_mem : a ∉ topCycleSet (P := P) := (Finset.mem_sdiff.mp ha).2
      have hb_mem : b ∈ topCycleSet (P := P) := by
        by_contra hb_not_mem
        exact hb (Finset.mem_sdiff.mpr ⟨by simp, hb_not_mem⟩)
      have hpos : margin_pos P b a := (topCycleSet_dominates (P := P)).2 b hb_mem a ha_not_mem
      simpa [margin_pos, margin_reverse_eq] using hpos
    have hsubset_rev :
        topCycleSet (P := reverse_profile P) ⊆
          ((Finset.univ : Finset A) \ topCycleSet (P := P)) :=
      topCycleSet_subset_of_dominates (P := reverse_profile P) hcomp_dominates
    have hdisj :
        topCycleSet (P := P) ∩ topCycleSet (P := reverse_profile P) = (∅ : Finset A) := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxP, hxR⟩
      exact (Finset.mem_sdiff.mp (hsubset_rev hxR)).2 hxP
    simpa [topCycle, hA] using hdisj
  · have huniv_empty : (Finset.univ : Finset A) = (∅ : Finset A) := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro a ha
      exact hA ⟨a⟩
    have hEq : topCycle P = (Finset.univ : Finset A) := by
      simp [topCycle, hA, huniv_empty]
    exact (hnot hEq).elim

end SocialChoice
