import SocialChoice.Axioms.Monotonicity
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

lemma dominatesSet_of_simpleLift {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x : A} {S : Finset A}
    (hLift : simpleLift P' P x) (hS : dominatesSet P' S) (hx : x ∉ S) :
    dominatesSet P S := by
  classical
  refine ⟨hS.1, ?_⟩
  intro a ha b hb
  by_cases hbx : b = x
  · subst hbx
    have hpos' : 0 < margin P' a b := by
      simpa [margin_pos] using (hS.2 a ha b hb)
    have hle : margin P' a b ≤ margin P a b :=
      margin_le_of_simpleLift_ax (P := P) (P' := P') (x := b) (a := a) hLift
    have hpos : 0 < margin P a b := lt_of_lt_of_le hpos' hle
    simpa [margin_pos] using hpos
  · have hax : a ≠ x := by
      intro hax
      subst hax
      exact hx ha
    have hEq : margin P a b = margin P' a b :=
      margin_eq_of_simpleLift P P' x a b hax hbx hLift
    have hpos' : margin_pos P' a b := hS.2 a ha b hb
    simpa [margin_pos, hEq] using hpos'

/-- TopCycle satisfies monotonicity under simple lifts. -/
theorem topCycle_monotonicity : Monotonicity topCycle := by
  intro V A _ _ P P' x hx hLift
  classical
  have hA : Nonempty A := ⟨x⟩
  let _ : Nonempty A := hA
  have hx' : x ∈ topCycleSet (P := P) := by
    simpa [topCycle, hA] using hx
  have hx_all : ∀ S, dominatesSet (P := P') S → x ∈ S := by
    intro S hS
    by_contra hxS
    have hS' : dominatesSet (P := P) S :=
      dominatesSet_of_simpleLift (P := P) (P' := P') (x := x) hLift hS hxS
    have hsubset : topCycleSet (P := P) ⊆ S :=
      topCycleSet_subset_of_dominates (P := P) hS'
    exact hxS (hsubset hx')
  have hx'' : x ∈ topCycleSet (P := P') :=
    hx_all (topCycleSet (P := P')) (topCycleSet_dominates (P := P'))
  simpa [topCycle, hA] using hx''

end SocialChoice
