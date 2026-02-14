import Pivato.Theorem1.PairwiseOrders
import Pivato.Theorem1.Representation

/-!
# Theorem 1 skewification helpers

This file isolates two ingredients needed for the paper-facing bridge from
perfect representations to perfect+skew representations:

- swap/negation transport lemmas for pairwise quotient infrastructure;
- a generic skewification constructor for balance systems.
-/

namespace Pivato

section PairwiseSwap

variable {V X : Type*} {D : Domain V}
variable {F : RuleOn D X}

/-- Swapping the pair indices in `pairwiseRel` reverses the relation arguments. -/
lemma pairwiseRel_swap_iff {x y : X} {a b : ZProfile V} :
    pairwiseRel F y x a b ↔ pairwiseRel F x y b a := by
  change b - a ∈ pairwiseDifferenceCone F y x ↔ a - b ∈ pairwiseDifferenceCone F x y
  constructor
  · intro h
    have hneg :
        -(b - a) ∈ pairwiseDifferenceCone F x y :=
      (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := x) (y := y)
        (z := b - a)).1 h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
  · intro h
    have hneg :
        -(a - b) ∈ pairwiseDifferenceCone F y x :=
      (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := y) (y := x)
        (z := a - b)).1 h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg

/-- The pairwise kernel subgroup is symmetric under swapping pair indices. -/
lemma pairwiseKernelSubgroup_swap_eq
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (x y : X) :
    pairwiseKernelSubgroup (F := F) hD hA hR y x =
      pairwiseKernelSubgroup (F := F) hD hA hR x y := by
  ext z
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · have hzxy : -(-z) ∈ pairwiseDifferenceCone F x y :=
        (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := x) (y := y)
          (z := -z)).1 hz.2
      simpa using hzxy
    · exact
        (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := x) (y := y)
          (z := z)).1 hz.1
  · intro hz
    refine ⟨?_, ?_⟩
    · have hzyx : -(-z) ∈ pairwiseDifferenceCone F y x :=
        (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := y) (y := x)
          (z := -z)).1 hz.2
      simpa using hzyx
    · exact
        (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := y) (y := x)
          (z := z)).1 hz.1

/-- Type-level symmetry of the pairwise quotient under index swap. -/
lemma pairwiseQuotient_swap_type_eq
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (x y : X) :
    PairwiseQuotient (F := F) hD hA hR y x =
      PairwiseQuotient (F := F) hD hA hR x y := by
  simp [PairwiseQuotient,
    pairwiseKernelSubgroup_swap_eq (F := F) hD hA hR x y]

end PairwiseSwap

section Skewification

variable {V X : Type*} {D : Domain V}
variable {R : Type*} [AddCommGroup R]

/-- Generic skewification of a balance system by antisymmetrization. -/
def skewifyBalanceSystem (B : BalanceSystem R X V) : BalanceSystem R X V where
  bal x y v := B.bal x y v - B.bal y x v

@[simp] lemma skewifyBalanceSystem_bal
    (B : BalanceSystem R X V) (x y : X) (v : V) :
    (skewifyBalanceSystem B).bal x y v = B.bal x y v - B.bal y x v :=
  rfl

lemma evalNat_sub [DecidableEq V]
    (w w' : V → R) (d : NProfile V) :
    evalNat (w := fun v => w v - w' v) d = evalNat (w := w) d - evalNat (w := w') d := by
  unfold evalNat
  simp [sub_eq_add_neg, nsmul_add]

lemma balanceAt_skewify [DecidableEq V]
    (B : BalanceSystem R X V) (x y : X) (d : NProfile V) :
    balanceAt (B := skewifyBalanceSystem B) x y d =
      balanceAt B x y d - balanceAt B y x d := by
  simpa [balanceAt, skewifyBalanceSystem] using
    (evalNat_sub (w := B.bal x y) (w' := B.bal y x) d)

/-- Antisymmetrization is always skew at aggregate balance level. -/
lemma skewifyBalanceSystem_skew [DecidableEq V]
    (B : BalanceSystem R X V) :
    BalanceSkew (B := skewifyBalanceSystem B) := by
  intro x y d
  calc
    balanceAt (B := skewifyBalanceSystem B) x y d
        = balanceAt B x y d - balanceAt B y x d :=
          balanceAt_skewify (B := B) x y d
    _ = -(balanceAt B y x d - balanceAt B x y d) := by
          simp [sub_eq_add_neg, add_comm]
    _ = -balanceAt (B := skewifyBalanceSystem B) y x d := by
          simp [balanceAt_skewify]

end Skewification

end Pivato
