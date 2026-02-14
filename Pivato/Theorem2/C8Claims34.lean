import Pivato.Theorem2.C8Claims12

/-!
# Lemma C.8 claims C.8.3 and C.8.4

This file records the two branch claims that produce a seed triple satisfying
the cocycle identity.
-/

namespace Pivato

section C8Claims34

universe uV uX uR

variable {V : Type uV} {X : Type uX} {R : Type uR}

/-- Claim C.8.3 branch:
from the "three-cycle / hull-equality" branch hypotheses, obtain a seed triple
with the cocycle identity. -/
theorem claimC83_seedTriple_of_threeCycleBranch
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hThreeCycleBranch :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
        (∀ ⦃d : NProfile V⦄, d ∈ D →
          balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0)) :
    ∃ x y z : X,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
        BalanceCocycleAtTriple D B x y z := by
  rcases hThreeCycleBranch with ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  refine ⟨x, y, z, hxy, hyz, hzx, ?_⟩
  intro d hd
  have hsum0 :
      (balanceAt B x y d + balanceAt B y z d) + balanceAt B z x d = 0 := by
    simpa [add_assoc] using hsum hd
  have hneg :
      balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d :=
    eq_neg_of_add_eq_zero_left hsum0
  calc
    balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d := hneg
    _ = balanceAt B x z d := by
      simp [hSkew z x d]

/-- Claim C.8.4 branch:
from the "four/five-cycle fallback" branch hypotheses, obtain a seed triple
with the cocycle identity. -/
theorem claimC84_seedTriple_of_fourFiveCycleBranch
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hFourFiveCycleBranch :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
        (∀ ⦃d : NProfile V⦄, d ∈ D →
          balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0)) :
    ∃ x y z : X,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
        BalanceCocycleAtTriple D B x y z := by
  rcases hFourFiveCycleBranch with ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  refine ⟨x, y, z, hxy, hyz, hzx, ?_⟩
  intro d hd
  have hsum0 :
      (balanceAt B x y d + balanceAt B y z d) + balanceAt B z x d = 0 := by
    simpa [add_assoc] using hsum hd
  have hneg :
      balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d :=
    eq_neg_of_add_eq_zero_left hsum0
  calc
    balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d := hneg
    _ = balanceAt B x z d := by
      simp [hSkew z x d]

end C8Claims34

end Pivato
