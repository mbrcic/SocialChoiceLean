import Mathlib.Data.Finset.Card
import SocialChoice.Axioms.Majority
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

lemma strictMajority_of_subset {V : Type} [Fintype V] {S T : Finset V}
    (hS : StrictMajority S) (hsub : S ⊆ T) : StrictMajority T := by
  unfold StrictMajority at *
  have hcard : S.card ≤ T.card := Finset.card_le_card hsub
  have hmul : 2 * S.card ≤ 2 * T.card := Nat.mul_le_mul_left 2 hcard
  exact lt_of_lt_of_le hS hmul

/-- TopCycle (Smith set) satisfies the mutual majority criterion. -/
theorem topCycle_mutualMajorityCriterion : MutualMajorityCriterion topCycle := by
  intro V A _ _ P S T hmaj hTne hpref
  classical
  rcases hTne with ⟨t, ht⟩
  have hA : Nonempty A := ⟨t⟩
  let _ : Nonempty A := hA
  have hdom : dominatesSet P T := by
    refine ⟨?_, ?_⟩
    · exact ⟨t, ht⟩
    · intro a ha b hb
      have hsub : S ⊆ votersPreferring P a b := by
        intro v hv
        have hp : Prefers P v a b := hpref v hv a ha b hb
        exact Finset.mem_filter.mpr ⟨by simp, hp⟩
      have hmaj' : StrictMajority (votersPreferring P a b) :=
        strictMajority_of_subset hmaj hsub
      have hne : a ≠ b := by
        intro hEq
        subst hEq
        exact hb ha
      exact (strictMajority_votersPreferring_iff_margin_pos
        (P := P) (c := a) (d := b) (hcd := hne)).1 hmaj'
  have hsubset : topCycleSet (P := P) ⊆ T :=
    topCycleSet_subset_of_dominates (P := P) hdom
  simpa [topCycle, hA] using hsubset

end SocialChoice
