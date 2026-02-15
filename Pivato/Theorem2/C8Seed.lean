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

/-- Eq. (C.21)-style seed hypothesis:
there exist distinct alternatives satisfying the three-cycle sum law over `D`. -/
def C8CycleSumHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  ∃ x y z : X,
    x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    (∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0)

/-- Branch split hypothesis used in Appendix C.8 before Claim C.8.5:
either the C.8.3 branch or the C.8.4 branch yields a triple-cycle sum law. -/
def C8BranchSplitHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  C8CycleSumHypothesis (D := D) (B := B) ∨
    C8CycleSumHypothesis (D := D) (B := B)

theorem branchSplit_of_cycleSumHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hCycle : C8CycleSumHypothesis (D := D) (B := B)) :
    C8BranchSplitHypothesis (D := D) (B := B) :=
  Or.inl hCycle

theorem cycleSumHypothesis_of_branchSplit
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hBranch : C8BranchSplitHypothesis (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hBranch with h | h
  · exact h
  · exact h

theorem c8BranchSplitHypothesis_iff_cycleSumHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V} :
    C8BranchSplitHypothesis (D := D) (B := B) ↔
      C8CycleSumHypothesis (D := D) (B := B) := by
  constructor
  · exact cycleSumHypothesis_of_branchSplit (D := D) (B := B)
  · exact branchSplit_of_cycleSumHypothesis (D := D) (B := B)

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
  rcases cycleSumHypothesis_of_branchSplit (D := D) (B := B) hBranch with
    ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  have hC83 :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          (∀ ⦃d : NProfile V⦄, d ∈ D →
            balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0) :=
    ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  exact claimC83_seedTriple_of_threeCycleBranch
      (D := D) (B := B) hSkew hC83

end C8Seed

end Pivato
