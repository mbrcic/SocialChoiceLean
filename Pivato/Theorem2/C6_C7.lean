import Pivato.Theorem2.C4_C5

/-!
# Stage F skeleton: Lemmas C.6 and C.7

This file records theorem-level interfaces for Appendix C.6 and C.7 as tracked
`sorry` goals.
-/

namespace Pivato

section C6_C7

universe uA uI

variable {A : Type uA}

/-- Cone predicate for subsets of an additive group (set-level analogue used in
Appendix C.7). -/
def IsConeSet [AddCommGroup A] (S : Set A) : Prop :=
  AdditivelyClosed S ∧
    ∀ ⦃a : A⦄ ⦃n : ℕ⦄, n ≠ 0 → n • a ∈ S → a ∈ S

/-- Lemma C.6:
if `S₁ ∪ S₂` is additively closed, then the divisible hull of the union equals
one of the two individual hulls. -/
theorem lemmaC6
    [AddCommGroup A]
    (S₁ S₂ : Set A)
    (K K₁ K₂ : AddSubgroup A)
    (hHull : IsDivisibleHull (S₁ ∪ S₂) K)
    (hHull₁ : IsDivisibleHull S₁ K₁)
    (hHull₂ : IsDivisibleHull S₂ K₂)
    (hAddClosed : AdditivelyClosed (S₁ ∪ S₂)) :
    K = K₁ ∨ K = K₂ := by
  sorry

/-- Lemma C.7:
for a finite family of cone-sets whose union is additively closed, one member
hull already equals the hull of the whole union. -/
theorem lemmaC7
    [AddCommGroup A] {ι : Type uI} [Fintype ι]
    (S : ι → Set A)
    (K : AddSubgroup A) (Kᵢ : ι → AddSubgroup A)
    (hHull : IsDivisibleHull (⋃ i, S i) K)
    (hHullᵢ : ∀ i, IsDivisibleHull (S i) (Kᵢ i))
    (hCone : ∀ i, IsConeSet (S i))
    (hAddClosed : AdditivelyClosed (⋃ i, S i)) :
    ∃ i, K = Kᵢ i := by
  sorry

end C6_C7

end Pivato

