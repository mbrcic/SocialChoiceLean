import Pivato.Theorem2.C8Claims34

/-!
# Lemma C.8 seed packaging

This file packages the Claim C.8.3 / C.8.4 branch split into the seed-triple
form (paper Eq. (C.21)) consumed by Claim C.8.5.
-/

namespace Pivato

section C8Seed

universe uV uX uR

variable {V : Type uV} {X : Type uX} {R : Type uR}

/-- Branch split hypothesis used in Appendix C.8 before Claim C.8.5:
either the C.8.3 branch or the C.8.4 branch yields a triple-cycle sum law. -/
def C8BranchSplitHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  (∃ x y z : X,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0)) ∨
    (∃ x y z : X,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0))

/-- Eq. (C.21) packaging:
from the C.8.3/C.8.4 branch split, obtain a seed triple satisfying
`BalanceCocycleAtTriple`. -/
theorem seedTriple_of_branchSplit
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hBranch : C8BranchSplitHypothesis (D := D) (B := B)) :
    ∃ x y z : X,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
        BalanceCocycleAtTriple D B x y z := by
  rcases hBranch with hC83 | hC84
  · exact claimC83_seedTriple_of_threeCycleBranch
      (D := D) (B := B) hSkew hC83
  · exact claimC84_seedTriple_of_fourFiveCycleBranch
      (D := D) (B := B) hSkew hC84

end C8Seed

end Pivato
