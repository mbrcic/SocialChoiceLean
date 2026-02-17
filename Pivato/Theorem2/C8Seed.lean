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

/-- Claim C.8.3 branch payload:
the resulting Eq. (C.21)-shape witness produced by the three-orbit branch. -/
inductive C8ThreeCycleBranchHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop where
  | intro
      (x y z : X)
      (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
      (eqC21 :
        ∀ ⦃d : NProfile V⦄, d ∈ D →
          balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0) :
      C8ThreeCycleBranchHypothesis D B

/-- Claim C.8.4 branch payload:
the resulting Eq. (C.21)-shape witness produced by the 4/5-cycle fallback branch. -/
inductive C8FourFiveCycleBranchHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop where
  | ofFourCycle
      (x y z w : X)
      (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
      (hzw : z ≠ w) (hwx : w ≠ x)
      (eqC21 :
        ∀ ⦃d : NProfile V⦄, d ∈ D →
          balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0) :
      C8FourFiveCycleBranchHypothesis D B
  | ofFiveCycle
      (x y z u v : X)
      (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
      (hzu : z ≠ u) (huv : u ≠ v) (hvx : v ≠ x)
      (eqC21 :
        ∀ ⦃d : NProfile V⦄, d ∈ D →
          balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0) :
      C8FourFiveCycleBranchHypothesis D B

def C8BranchSplitHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  C8ThreeCycleBranchHypothesis (D := D) (B := B) ∨
    C8FourFiveCycleBranchHypothesis (D := D) (B := B)

theorem branchSplit_of_cycleSumHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hCycle : C8CycleSumHypothesis (D := D) (B := B)) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases hCycle with ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  exact Or.inl ⟨x, y, z, hxy, hyz, hzx, hsum⟩

theorem threeCycleBranch_of_cycleSumHypothesis
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hCycle : C8CycleSumHypothesis (D := D) (B := B)) :
    C8ThreeCycleBranchHypothesis (D := D) (B := B) := by
  rcases hCycle with ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  exact ⟨x, y, z, hxy, hyz, hzx, hsum⟩

theorem cycleSumHypothesis_of_threeCycleBranch
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hC83 : C8ThreeCycleBranchHypothesis (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hC83 with ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  exact ⟨x, y, z, hxy, hyz, hzx, hsum⟩

theorem cycleSumHypothesis_of_fourFiveCycleBranch
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hC84 : C8FourFiveCycleBranchHypothesis (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  cases hC84 with
  | ofFourCycle x y z _w hxy hyz hzx _hzw _hwx hsum =>
      exact ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  | ofFiveCycle x y z _u _v hxy hyz hzx _hzu _huv _hvx hsum =>
      exact ⟨x, y, z, hxy, hyz, hzx, hsum⟩

theorem cycleSumHypothesis_of_branchSplit
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hBranch : C8BranchSplitHypothesis (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hBranch with hC83 | hC84
  · exact cycleSumHypothesis_of_threeCycleBranch (D := D) (B := B) hC83
  · exact cycleSumHypothesis_of_fourFiveCycleBranch (D := D) (B := B) hC84

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
  rcases hBranch with hC83 | hC84
  · exact claimC83_seedTriple_of_threeCycleBranch
      (D := D) (B := B) hSkew
      (cycleSumHypothesis_of_threeCycleBranch (D := D) (B := B) hC83)
  · exact claimC84_seedTriple_of_fourFiveCycleBranch
      (D := D) (B := B) hSkew
      (cycleSumHypothesis_of_fourFiveCycleBranch (D := D) (B := B) hC84)

end C8Seed

end Pivato
