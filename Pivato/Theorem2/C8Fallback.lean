import Pivato.Theorem2.C8OrbitCases
import Pivato.Theorem1.Representation

/-!
# Lemma C.8.4 fallback packaging

This file stages the C.8.4 fallback path into smaller lemmas:
- package-generation in the `% 3 = 1` and `% 3 = 2` regimes;
- conversion from fallback package to the C.8 branch hypothesis.

It introduces explicit 4-cycle / 5-cycle equation-pack predicates as a
paper-facing target shape for C.9--C.20 style fallback equations.
-/

namespace Pivato

section C8Fallback

universe uV uX uR

variable {V : Type uV} {X : Type uX} {R : Type uR}
variable (nu : Equiv.Perm X →* Equiv.Perm V)

/-- C.8.4 fallback package: 4-cycle equations (C.9--C.14 style). -/
structure C8FallbackEquationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) where
  x : X
  y : X
  z : X
  w : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hzw : z ≠ w
  hwx : w ≠ x
  eqC9 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d +
        balanceAt B z w d + balanceAt B w x d = 0
  eqC10 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d = balanceAt B x z d
  eqC11 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z w d = balanceAt B y w d
  eqC12 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z w d + balanceAt B w x d = balanceAt B z x d
  eqC13 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B w x d + balanceAt B x y d = balanceAt B w y d
  eqC14 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x z d + balanceAt B z w d = balanceAt B x w d

/-- C.8.4 fallback package: 5-cycle equations (C.15--C.20 style). -/
structure C8FallbackEquationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) where
  x : X
  y : X
  z : X
  u : X
  v : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hzu : z ≠ u
  huv : u ≠ v
  hvx : v ≠ x
  eqC15 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d = 0
  eqC16 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d = balanceAt B x z d
  eqC17 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z u d = balanceAt B y u d
  eqC18 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z u d + balanceAt B u v d = balanceAt B z v d
  eqC19 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B u v d + balanceAt B v x d = balanceAt B u x d
  eqC20 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z v d + balanceAt B v x d = balanceAt B z x d

/-- C.8.4 fallback equation package: either the 4-cycle or 5-cycle package. -/
def C8FallbackEquationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) ∨
    Nonempty (C8FallbackEquationPack5 (D := D) (B := B))

lemma c8Fallback_balanceAt_diag_eq_zero_of_skew
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (a : X) (d : NProfile V) :
    balanceAt B a a d = (0 : R) := by
  let t : R := balanceAt B a a d
  have hsk : t = -t := by
    simpa [t] using (hSkew a a d)
  have hsum : t + t = 0 := by
    calc
      t + t = t + (-t) := by
        nth_rewrite 2 [hsk]
        rfl
      _ = 0 := by simp
  have htwo :
      (2 : ℕ) • t = (2 : ℕ) • (0 : R) := by
    simpa [two_nsmul] using hsum
  have ht0 : t = 0 :=
    (nsmul_right_injective (M := R) (by decide : (2 : ℕ) ≠ 0)) htwo
  simpa [t] using ht0

lemma c8Fallback_eqC10_of_cycleSum
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {x y z : X}
    (hCycle :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d = balanceAt B x z d := by
  intro d hd
  have hsum0 :
      (balanceAt B x y d + balanceAt B y z d) + balanceAt B z x d = 0 := by
    simpa [add_assoc] using hCycle hd
  have hneg :
      balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d :=
    eq_neg_of_add_eq_zero_left hsum0
  calc
    balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d := hneg
    _ = balanceAt B x z d := by simp [hSkew z x d]

/-- Case-1 paper-aligned reduction:
from the six 4-term equations (C.9)--(C.14), derive the reduced cocycle form
`b(x,y)+b(y,z)=b(x,z)`.  Algebraically only (C.9)--(C.11) are independent;
(C.12)--(C.14) are included to match paper structure. -/
lemma c8Fallback_eqC10_of_case1_sixEquations
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {x y z w : X}
    (hE9 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d = 0)
    (hE10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y w d + balanceAt B w z d + balanceAt B z x d = 0)
    (hE11 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z x d + balanceAt B x w d + balanceAt B w y d = 0)
    (_hE12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z w d + balanceAt B w x d + balanceAt B x y d = 0)
    (_hE13 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z x d + balanceAt B x y d + balanceAt B y w d + balanceAt B w z d = 0)
    (_hE14 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z x d + balanceAt B x w d + balanceAt B w y d + balanceAt B y z d = 0) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d = balanceAt B x z d := by
  intro d hd
  have hTwo :
      (2 : ℕ) • (balanceAt B x y d + balanceAt B y z d + balanceAt B z x d) = 0 := by
    calc
      (2 : ℕ) • (balanceAt B x y d + balanceAt B y z d + balanceAt B z x d)
          = (balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d) +
              (balanceAt B x y d + balanceAt B y w d + balanceAt B w z d + balanceAt B z x d) +
              (balanceAt B y z d + balanceAt B z x d + balanceAt B x w d + balanceAt B w y d) := by
                simp [two_nsmul, add_assoc, add_left_comm, add_comm,
                  hSkew w x d, hSkew w z d, hSkew w y d]
      _ = 0 := by simp [hE9 hd, hE10 hd, hE11 hd]
  have hCycle :
      balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0 :=
    (nsmul_right_injective (M := R) (by decide : (2 : ℕ) ≠ 0)) (by simpa using hTwo)
  have hsum0 :
      (balanceAt B x y d + balanceAt B y z d) + balanceAt B z x d = 0 := by
    simpa [add_assoc] using hCycle
  have hneg :
      balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d :=
    eq_neg_of_add_eq_zero_left hsum0
  calc
    balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d := hneg
    _ = balanceAt B x z d := by simp [hSkew z x d]

/-- From Case-1 paper equation (C.9), derive (C.10) by relabeling with the
swap `(z w)` and transporting back via neutrality/domain-invariance. -/
lemma c8Fallback_eqC10p_of_eqC9_swap
    [DecidableEq X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {x y z w : X}
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hC9 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d = 0) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y w d + balanceAt B w z d + balanceAt B z x d = 0 := by
  intro d hd
  let τ : Equiv.Perm X := Equiv.swap z w
  let dτ : NProfile V := permuteNProfile (nu τ) d
  have hdτ : dτ ∈ D := by
    change permuteNProfile (nu τ) d ∈ D
    exact hInv τ hd
  have h9τ :
      balanceAt B x y dτ + balanceAt B y z dτ + balanceAt B z w dτ + balanceAt B w x dτ = 0 :=
    hC9 hdτ
  have hxy : balanceAt B x y dτ = balanceAt B x y d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB τ x y d
    simpa [dτ, τ, Equiv.swap_apply_of_ne_of_ne hxz hxw, Equiv.swap_apply_of_ne_of_ne hyz hyw]
      using hBase
  have hyw' : balanceAt B y z dτ = balanceAt B y w d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB τ y w d
    simpa [dτ, τ, Equiv.swap_apply_of_ne_of_ne hyz hyw] using hBase
  have hwz : balanceAt B z w dτ = balanceAt B w z d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB τ w z d
    simpa [dτ, τ] using hBase
  have hzx' : balanceAt B w x dτ = balanceAt B z x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB τ z x d
    simpa [dτ, τ, Equiv.swap_apply_of_ne_of_ne hxz hxw] using hBase
  calc
    balanceAt B x y d + balanceAt B y w d + balanceAt B w z d + balanceAt B z x d
        = balanceAt B x y dτ + balanceAt B y z dτ + balanceAt B z w dτ + balanceAt B w x dτ := by
            simp [hxy, hyw', hwz, hzx', add_assoc, add_left_comm, add_comm]
    _ = 0 := h9τ

/-- From Case-1 paper equation (C.10), derive (C.11) by rotation under the
designated 4-cycle permutation. -/
lemma c8Fallback_eqC11p_of_eqC10p_rotate
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z w : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = w) (hφw : φ w = x)
    (hC10p :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y w d + balanceAt B w z d + balanceAt B z x d = 0) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d + balanceAt B x w d + balanceAt B w y d = 0 := by
  intro d hd
  let d3 : NProfile V := permuteNProfile (nu (φ ^ 3)) d
  have hd3 : d3 ∈ D := by
    change (permuteNProfile (nu (φ ^ 3))) d ∈ D
    exact hInv (φ ^ 3) hd
  have hφ3x : (φ ^ 3) x = w := by
    calc
      (φ ^ 3) x = φ ((φ ^ 2) x) := by simp [pow_succ']
      _ = φ (φ (φ x)) := by simp [pow_succ']
      _ = w := by simp [hφx, hφy, hφz]
  have hφ3y : (φ ^ 3) y = x := by
    calc
      (φ ^ 3) y = φ ((φ ^ 2) y) := by simp [pow_succ']
      _ = φ (φ (φ y)) := by simp [pow_succ']
      _ = x := by simp [hφy, hφz, hφw]
  have hφ3z : (φ ^ 3) z = y := by
    calc
      (φ ^ 3) z = φ ((φ ^ 2) z) := by simp [pow_succ']
      _ = φ (φ (φ z)) := by simp [pow_succ']
      _ = y := by simp [hφz, hφw, hφx]
  have hφ3w : (φ ^ 3) w = z := by
    calc
      (φ ^ 3) w = φ ((φ ^ 2) w) := by simp [pow_succ']
      _ = φ (φ (φ w)) := by simp [pow_succ']
      _ = z := by simp [hφw, hφx, hφy]
  have h1 : balanceAt B x y d3 = balanceAt B y z d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB (φ ^ 3) y z d
    simpa [d3, hφ3y, hφ3z] using hBase
  have h2 : balanceAt B y w d3 = balanceAt B z x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB (φ ^ 3) z x d
    simpa [d3, hφ3z, hφ3x] using hBase
  have h3 : balanceAt B w z d3 = balanceAt B x w d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB (φ ^ 3) x w d
    simpa [d3, hφ3x, hφ3w] using hBase
  have h4 : balanceAt B z x d3 = balanceAt B w y d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B) hNeutralB (φ ^ 3) w y d
    simpa [d3, hφ3w, hφ3y] using hBase
  calc
    balanceAt B y z d + balanceAt B z x d + balanceAt B x w d + balanceAt B w y d
        = balanceAt B x y d3 + balanceAt B y w d3 + balanceAt B w z d3 + balanceAt B z x d3 := by
            simp [h1, h2, h3, h4, add_assoc, add_comm]
    _ = 0 := hC10p hd3

lemma c8Fallback_eqC9_of_eqC10_eqC12
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {x y z w : X}
    (hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d)
    (hC12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z w d + balanceAt B w x d = balanceAt B z x d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d +
        balanceAt B z w d + balanceAt B w x d = 0 := by
  intro d hd
  calc
    balanceAt B x y d + balanceAt B y z d +
        balanceAt B z w d + balanceAt B w x d
        = balanceAt B x z d + balanceAt B z x d := by
            simp [hC10 hd, hC12 hd, add_assoc]
    _ = 0 := by
          calc
            balanceAt B x z d + balanceAt B z x d
                = balanceAt B x z d + (-balanceAt B x z d) := by
                    simp [hSkew z x d]
            _ = 0 := by simp

lemma c8Fallback_eqC14_of_eqC12
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {x z w : X}
    (hC12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z w d + balanceAt B w x d = balanceAt B z x d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x z d + balanceAt B z w d = balanceAt B x w d := by
  intro d hd
  have hZw : balanceAt B z w d = balanceAt B z x d - balanceAt B w x d :=
    (eq_sub_iff_add_eq).2 (hC12 hd)
  calc
    balanceAt B x z d + balanceAt B z w d
        = balanceAt B x z d + (balanceAt B z x d - balanceAt B w x d) := by
            simp [hZw]
    _ = (balanceAt B x z d + balanceAt B z x d) - balanceAt B w x d := by
          simp [sub_eq_add_neg, add_assoc]
    _ = (balanceAt B x z d + (-balanceAt B x z d)) - balanceAt B w x d := by
          simp [hSkew z x d]
    _ = 0 - balanceAt B w x d := by simp
    _ = -balanceAt B w x d := by simp
    _ = balanceAt B x w d := by simp [hSkew w x d]

lemma c8Fallback_eqC13_of_eqC10_eqC11_eqC12
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {w x y z : X}
    (hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d)
    (hC11 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z w d = balanceAt B y w d)
    (hC12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z w d + balanceAt B w x d = balanceAt B z x d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B w x d + balanceAt B x y d = balanceAt B w y d := by
  intro d hd
  have hxy : balanceAt B x y d = balanceAt B x z d - balanceAt B y z d :=
    (eq_sub_iff_add_eq).2 (hC10 hd)
  have hwx : balanceAt B w x d = balanceAt B z x d - balanceAt B z w d :=
    (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hC12 hd)
  calc
    balanceAt B w x d + balanceAt B x y d
        = (balanceAt B z x d - balanceAt B z w d) +
            (balanceAt B x z d - balanceAt B y z d) := by
              simp [hxy, hwx]
    _ = (balanceAt B z x d + balanceAt B x z d) -
          (balanceAt B z w d + balanceAt B y z d) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = (balanceAt B z x d + balanceAt B x z d) -
          (balanceAt B y z d + balanceAt B z w d) := by
            simp [add_comm]
    _ = 0 - (balanceAt B y z d + balanceAt B z w d) := by
          simp [hSkew x z d]
    _ = -(balanceAt B y z d + balanceAt B z w d) := by simp
    _ = -balanceAt B y w d := by simp [hC11 hd]
    _ = balanceAt B w y d := by simp [hSkew y w d]

lemma c8Fallback_eqC15_of_eqC16_eqC18_eqC20
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {x y z u v : X}
    (hC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d)
    (hC18 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z u d + balanceAt B u v d = balanceAt B z v d)
    (hC20 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z v d + balanceAt B v x d = balanceAt B z x d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d = 0 := by
  intro d hd
  calc
    balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d
        = (balanceAt B x y d + balanceAt B y z d) +
            ((balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d) := by
              simp [add_assoc]
    _ = balanceAt B x z d + (balanceAt B z v d + balanceAt B v x d) := by
          simp [hC16 hd, hC18 hd]
    _ = balanceAt B x z d + balanceAt B z x d := by simp [hC20 hd]
    _ = 0 := by
          calc
            balanceAt B x z d + balanceAt B z x d
                = balanceAt B x z d + (-balanceAt B x z d) := by
                    simp [hSkew z x d]
            _ = 0 := by simp

lemma c8Fallback_eqC20_of_eqC15_eqC16_eqC18
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    {x y z u v : X}
    (hC15 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
          balanceAt B u v d + balanceAt B v x d = 0)
    (hC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d)
    (hC18 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z u d + balanceAt B u v d = balanceAt B z v d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z v d + balanceAt B v x d = balanceAt B z x d := by
  intro d hd
  have h15 :
      (balanceAt B x y d + balanceAt B y z d) +
        ((balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d) = 0 := by
    simpa [add_assoc] using hC15 hd
  have hZvVx :
      balanceAt B z v d + balanceAt B v x d =
        - (balanceAt B x y d + balanceAt B y z d) := by
    calc
      balanceAt B z v d + balanceAt B v x d
          = (balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d := by
              simp [hC18 hd]
      _ = - (balanceAt B x y d + balanceAt B y z d) := by
            exact eq_neg_of_add_eq_zero_right h15
  calc
    balanceAt B z v d + balanceAt B v x d
        = - (balanceAt B x y d + balanceAt B y z d) := hZvVx
    _ = -balanceAt B x z d := by simp [hC16 hd]
    _ = balanceAt B z x d := by simp [hSkew z x d]

lemma c8Fallback_eqC11_of_eqC10_rotate
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z w : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = w) (hφw : φ w = x)
    (hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z w d = balanceAt B y w d := by
  intro d hd
  let d3 : NProfile V := permuteNProfile (nu (φ ^ 3)) d
  have hd3 : d3 ∈ D := by
    change (permuteNProfile (nu (φ ^ 3))) d ∈ D
    exact hInv (φ ^ 3) hd
  have hφ3y : (φ ^ 3) y = x := by
    calc
      (φ ^ 3) y = φ ((φ ^ 2) y) := by simp [pow_succ']
      _ = φ (φ (φ y)) := by simp [pow_succ']
      _ = x := by simp [hφy, hφz, hφw]
  have hφ3z : (φ ^ 3) z = y := by
    calc
      (φ ^ 3) z = φ ((φ ^ 2) z) := by simp [pow_succ']
      _ = φ (φ (φ z)) := by simp [pow_succ']
      _ = y := by simp [hφz, hφw, hφx]
  have hφ3w : (φ ^ 3) w = z := by
    calc
      (φ ^ 3) w = φ ((φ ^ 2) w) := by simp [pow_succ']
      _ = φ (φ (φ w)) := by simp [pow_succ']
      _ = z := by simp [hφw, hφx, hφy]
  have hTerm1 :
      balanceAt B x y d3 = balanceAt B y z d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) y z d
    simpa [d3, MonoidHom.map_pow, hφ3y, hφ3z] using hBase
  have hTerm2 :
      balanceAt B y z d3 = balanceAt B z w d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) z w d
    simpa [d3, MonoidHom.map_pow, hφ3z, hφ3w] using hBase
  have hTerm3 :
      balanceAt B x z d3 = balanceAt B y w d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) y w d
    simpa [d3, MonoidHom.map_pow, hφ3y, hφ3w] using hBase
  calc
    balanceAt B y z d + balanceAt B z w d
        = balanceAt B x y d3 + balanceAt B y z d3 := by
            simp [hTerm1, hTerm2]
    _ = balanceAt B x z d3 := hC10 hd3
    _ = balanceAt B y w d := hTerm3

lemma c8Fallback_eqC12_of_eqC10_rotate
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z w : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = w) (hφw : φ w = x)
    (hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z w d + balanceAt B w x d = balanceAt B z x d := by
  intro d hd
  let d2 : NProfile V := permuteNProfile (nu (φ ^ 2)) d
  have hd2 : d2 ∈ D := by
    change (permuteNProfile (nu (φ ^ 2))) d ∈ D
    exact hInv (φ ^ 2) hd
  have hφ2x : (φ ^ 2) x = z := by
    calc
      (φ ^ 2) x = φ (φ x) := by simp [pow_succ']
      _ = z := by simp [hφx, hφy]
  have hφ2w : (φ ^ 2) w = y := by
    calc
      (φ ^ 2) w = φ (φ w) := by simp [pow_succ']
      _ = y := by simp [hφw, hφx]
  have hφ2z : (φ ^ 2) z = x := by
    calc
      (φ ^ 2) z = φ (φ z) := by simp [pow_succ']
      _ = x := by simp [hφz, hφw]
  have hTerm1 :
      balanceAt B x y d2 = balanceAt B z w d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) z w d
    simpa [d2, MonoidHom.map_pow, hφ2z, hφ2w] using hBase
  have hTerm2 :
      balanceAt B y z d2 = balanceAt B w x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) w x d
    simpa [d2, MonoidHom.map_pow, hφ2w, hφ2x] using hBase
  have hTerm3 :
      balanceAt B x z d2 = balanceAt B z x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) z x d
    simpa [d2, MonoidHom.map_pow, hφ2z, hφ2x] using hBase
  calc
    balanceAt B z w d + balanceAt B w x d
        = balanceAt B x y d2 + balanceAt B y z d2 := by
            simp [hTerm1, hTerm2]
    _ = balanceAt B x z d2 := hC10 hd2
    _ = balanceAt B z x d := hTerm3

lemma c8Fallback_eqC17_of_eqC16_rotate
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z u v : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = u)
    (hφu : φ u = v) (hφv : φ v = x)
    (hC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z u d = balanceAt B y u d := by
  intro d hd
  let d4 : NProfile V := permuteNProfile (nu (φ ^ 4)) d
  have hd4 : d4 ∈ D := by
    change (permuteNProfile (nu (φ ^ 4))) d ∈ D
    exact hInv (φ ^ 4) hd
  have hφ4y : (φ ^ 4) y = x := by
    calc
      (φ ^ 4) y = φ ((φ ^ 3) y) := by simp [pow_succ']
      _ = φ (φ (φ (φ y))) := by simp [pow_succ']
      _ = x := by simp [hφy, hφz, hφu, hφv]
  have hφ4z : (φ ^ 4) z = y := by
    calc
      (φ ^ 4) z = φ ((φ ^ 3) z) := by simp [pow_succ']
      _ = φ (φ (φ (φ z))) := by simp [pow_succ']
      _ = y := by simp [hφz, hφu, hφv, hφx]
  have hφ4u : (φ ^ 4) u = z := by
    calc
      (φ ^ 4) u = φ ((φ ^ 3) u) := by simp [pow_succ']
      _ = φ (φ (φ (φ u))) := by simp [pow_succ']
      _ = z := by simp [hφu, hφv, hφx, hφy]
  have hTerm1 :
      balanceAt B x y d4 = balanceAt B y z d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 4) y z d
    simpa [d4, hφ4y, hφ4z] using hBase
  have hTerm2 :
      balanceAt B y z d4 = balanceAt B z u d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 4) z u d
    simpa [d4, hφ4z, hφ4u] using hBase
  have hTerm3 :
      balanceAt B x z d4 = balanceAt B y u d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 4) y u d
    simpa [d4, hφ4y, hφ4u] using hBase
  calc
    balanceAt B y z d + balanceAt B z u d
        = balanceAt B x y d4 + balanceAt B y z d4 := by
            simp [hTerm1, hTerm2]
    _ = balanceAt B x z d4 := hC16 hd4
    _ = balanceAt B y u d := hTerm3

lemma c8Fallback_eqC18_of_eqC16_rotate
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z u v : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = u)
    (hφu : φ u = v) (hφv : φ v = x)
    (hC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z u d + balanceAt B u v d = balanceAt B z v d := by
  intro d hd
  let d3 : NProfile V := permuteNProfile (nu (φ ^ 3)) d
  have hd3 : d3 ∈ D := by
    change (permuteNProfile (nu (φ ^ 3))) d ∈ D
    exact hInv (φ ^ 3) hd
  have hφ3z : (φ ^ 3) z = x := by
    calc
      (φ ^ 3) z = φ ((φ ^ 2) z) := by simp [pow_succ']
      _ = φ (φ (φ z)) := by simp [pow_succ']
      _ = x := by simp [hφz, hφu, hφv]
  have hφ3u : (φ ^ 3) u = y := by
    calc
      (φ ^ 3) u = φ ((φ ^ 2) u) := by simp [pow_succ']
      _ = φ (φ (φ u)) := by simp [pow_succ']
      _ = y := by simp [hφu, hφv, hφx]
  have hφ3v : (φ ^ 3) v = z := by
    calc
      (φ ^ 3) v = φ ((φ ^ 2) v) := by simp [pow_succ']
      _ = φ (φ (φ v)) := by simp [pow_succ']
      _ = z := by simp [hφv, hφx, hφy]
  have hTerm1 :
      balanceAt B x y d3 = balanceAt B z u d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) z u d
    simpa [d3, hφ3z, hφ3u] using hBase
  have hTerm2 :
      balanceAt B y z d3 = balanceAt B u v d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) u v d
    simpa [d3, hφ3u, hφ3v] using hBase
  have hTerm3 :
      balanceAt B x z d3 = balanceAt B z v d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) z v d
    simpa [d3, hφ3z, hφ3v] using hBase
  calc
    balanceAt B z u d + balanceAt B u v d
        = balanceAt B x y d3 + balanceAt B y z d3 := by
            simp [hTerm1, hTerm2]
    _ = balanceAt B x z d3 := hC16 hd3
    _ = balanceAt B z v d := hTerm3

lemma c8Fallback_eqC19_of_eqC16_rotate
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z u v : X}
    (hφx : φ x = y) (hφy : φ y = z) (_hφz : φ z = u)
    (hφu : φ u = v) (hφv : φ v = x)
    (hC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B u v d + balanceAt B v x d = balanceAt B u x d := by
  intro d hd
  let d2 : NProfile V := permuteNProfile (nu (φ ^ 2)) d
  have hd2 : d2 ∈ D := by
    change (permuteNProfile (nu (φ ^ 2))) d ∈ D
    exact hInv (φ ^ 2) hd
  have hφ2u : (φ ^ 2) u = x := by
    calc
      (φ ^ 2) u = φ (φ u) := by simp [pow_succ']
      _ = x := by simp [hφu, hφv]
  have hφ2v : (φ ^ 2) v = y := by
    calc
      (φ ^ 2) v = φ (φ v) := by simp [pow_succ']
      _ = y := by simp [hφv, hφx]
  have hφ2x : (φ ^ 2) x = z := by
    calc
      (φ ^ 2) x = φ (φ x) := by simp [pow_succ']
      _ = z := by simp [hφx, hφy]
  have hTerm1 :
      balanceAt B x y d2 = balanceAt B u v d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) u v d
    simpa [d2, hφ2u, hφ2v] using hBase
  have hTerm2 :
      balanceAt B y z d2 = balanceAt B v x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) v x d
    simpa [d2, hφ2v, hφ2x] using hBase
  have hTerm3 :
      balanceAt B x z d2 = balanceAt B u x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) u x d
    simpa [d2, hφ2u, hφ2x] using hBase
  calc
    balanceAt B u v d + balanceAt B v x d
        = balanceAt B x y d2 + balanceAt B y z d2 := by
            simp [hTerm1, hTerm2]
    _ = balanceAt B x z d2 := hC16 hd2
    _ = balanceAt B u x d := hTerm3

noncomputable def c8FallbackOrbitMap4
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (c4 : C8Cycle4OrbitData X) : NProfile V → NProfile V :=
  orbitProfileSum (nu c4.φ) 3

noncomputable def c8FallbackOrbitMap5
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (c5 : C8Cycle5OrbitData X) : NProfile V → NProfile V :=
  orbitProfileSum (nu c5.φ) 4

noncomputable def c8FallbackBlockDomain4
    [AddCommMonoid R] [Preorder R] [Zero R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (c4 : C8Cycle4OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D) :
    Domain V :=
  orbitBlockDomain D (balanceRule (D := D) B)
    (c8FallbackOrbitMap4 (nu := nu) c4)
    (by
      intro d hd
      exact horbit hd)
    (orbitSet c4.φ c4.x)

noncomputable def c8FallbackBlockDomain5
    [AddCommMonoid R] [Preorder R] [Zero R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (c5 : C8Cycle5OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap5 (nu := nu) c5 d ∈ D) :
    Domain V :=
  orbitBlockDomain D (balanceRule (D := D) B)
    (c8FallbackOrbitMap5 (nu := nu) c5)
    (by
      intro d hd
      exact horbit hd)
    (orbitSet c5.φ c5.x)

def c8FallbackC10Weight
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c4 : C8Cycle4OrbitData X) : V → R :=
  fun v => B.bal c4.x c4.y v + B.bal c4.y c4.z v - B.bal c4.x c4.z v

def c8FallbackC16Weight
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c5 : C8Cycle5OrbitData X) : V → R :=
  fun v => B.bal c5.x c5.y v + B.bal c5.y c5.z v - B.bal c5.x c5.z v

def c8FallbackC15Weight
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c5 : C8Cycle5OrbitData X) : V → R :=
  fun v =>
    B.bal c5.x c5.y v + B.bal c5.y c5.z v + B.bal c5.z c5.u v +
      B.bal c5.u c5.v v + B.bal c5.v c5.x v

noncomputable def c8FallbackC10Hom
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c4 : C8Cycle4OrbitData X) : ZProfile V →+ R :=
  evalIntHom (c8FallbackC10Weight (B := B) c4)

noncomputable def c8FallbackC16Hom
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c5 : C8Cycle5OrbitData X) : ZProfile V →+ R :=
  evalIntHom (c8FallbackC16Weight (B := B) c5)

noncomputable def c8FallbackC15Hom
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c5 : C8Cycle5OrbitData X) : ZProfile V →+ R :=
  evalIntHom (c8FallbackC15Weight (B := B) c5)

lemma c8FallbackC10Hom_toZProfile
    [DecidableEq V]
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c4 : C8Cycle4OrbitData X)
    (d : NProfile V) :
    c8FallbackC10Hom (B := B) c4 (toZProfile d) =
      balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d - balanceAt B c4.x c4.z d := by
  unfold c8FallbackC10Hom
  rw [evalIntHom_toZProfile]
  unfold c8FallbackC10Weight
  simp [balanceAt, evalNat, add_assoc, sub_eq_add_neg]

lemma c8FallbackC16Hom_toZProfile
    [DecidableEq V]
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c5 : C8Cycle5OrbitData X)
    (d : NProfile V) :
    c8FallbackC16Hom (B := B) c5 (toZProfile d) =
      balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d - balanceAt B c5.x c5.z d := by
  unfold c8FallbackC16Hom
  rw [evalIntHom_toZProfile]
  unfold c8FallbackC16Weight
  simp [balanceAt, evalNat, add_assoc, sub_eq_add_neg]

lemma c8FallbackC15Hom_toZProfile
    [DecidableEq V]
    [AddCommGroup R]
    (B : BalanceSystem R X V)
    (c5 : C8Cycle5OrbitData X)
    (d : NProfile V) :
    c8FallbackC15Hom (B := B) c5 (toZProfile d) =
      balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d + balanceAt B c5.z c5.u d +
        balanceAt B c5.u c5.v d + balanceAt B c5.v c5.x d := by
  unfold c8FallbackC15Hom
  rw [evalIntHom_toZProfile]
  unfold c8FallbackC15Weight
  simp [balanceAt, evalNat, add_assoc]

/-- Generic 4-cycle block-domain equation:
from one concrete 4-cycle permutation, derive the corresponding 4-term zero
sum on the associated block-domain. -/
lemma c8Fallback_cycle4_sum_on_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z w : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = w) (hφw : φ w = x)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitProfileSum (nu φ) 3 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ orbitBlockDomain D (balanceRule (D := D) B)
        (orbitProfileSum (nu φ) 3)
        (by
          intro d hd
          exact horbit hd)
        (orbitSet φ x) →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d = 0 := by
  intro d hd
  rcases hd with ⟨hdD, hBlock⟩
  have hxWin :
      x ∈ balanceRule (D := D) B ⟨orbitProfileSum (nu φ) 3 d, horbit hdD⟩ :=
    hBlock (self_mem_orbitSet φ x)
  have hyWin :
      y ∈ balanceRule (D := D) B ⟨orbitProfileSum (nu φ) 3 d, horbit hdD⟩ := by
    refine hBlock ?_
    exact ⟨1, hφx⟩
  have hxyZero :
      balanceAt B x y (orbitProfileSum (nu φ) 3 d) = 0 :=
    balanceAt_eq_zero_of_two_winners
      (D := D) B hSkew (hd := horbit hdD) hxWin hyWin
  have hTerm1 :
      balanceAt B x y (permuteNProfile (nu φ) d) =
        balanceAt B w x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB φ w x d
    simpa [hφw, hφx] using hBase
  have hφ2z : (φ ^ 2) z = x := by
    calc
      (φ ^ 2) z = φ (φ z) := by simp [pow_succ']
      _ = x := by simp [hφz, hφw]
  have hφ2w : (φ ^ 2) w = y := by
    calc
      (φ ^ 2) w = φ (φ w) := by simp [pow_succ']
      _ = y := by simp [hφw, hφx]
  have hTerm2 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) =
        balanceAt B z w d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) z w d
    simpa [MonoidHom.map_pow, hφ2z, hφ2w] using hBase
  have hφ3y : (φ ^ 3) y = x := by
    calc
      (φ ^ 3) y = φ ((φ ^ 2) y) := by simp [pow_succ']
      _ = φ (φ (φ y)) := by simp [pow_succ']
      _ = x := by simp [hφy, hφz, hφw]
  have hφ3z : (φ ^ 3) z = y := by
    calc
      (φ ^ 3) z = φ ((φ ^ 2) z) := by simp [pow_succ']
      _ = φ (φ (φ z)) := by simp [pow_succ']
      _ = y := by simp [hφz, hφw, hφx]
  have hTerm3 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) =
        balanceAt B y z d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) y z d
    simpa [MonoidHom.map_pow, hφ3y, hφ3z] using hBase
  have hExpand :
      balanceAt B x y (orbitProfileSum (nu φ) 3 d) =
        balanceAt B x y d +
          balanceAt B x y (permuteNProfile (nu φ) d) +
            balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) := by
    unfold orbitProfileSum
    simp [Finset.sum_range_succ, balanceAt_add, add_assoc]
  calc
    balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d
        = balanceAt B x y d +
            balanceAt B x y (permuteNProfile (nu φ) d) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) +
                balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) := by
            simp [hTerm1, hTerm2, hTerm3, add_assoc, add_left_comm, add_comm]
    _ = balanceAt B x y (orbitProfileSum (nu φ) 3 d) := hExpand.symm
    _ = 0 := hxyZero

/-- Generic 5-cycle block-domain equation:
from one concrete 5-cycle permutation, derive the corresponding 5-term zero
sum on the associated block-domain. -/
lemma c8Fallback_cycle5_sum_on_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {x y z u v : X}
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = u)
    (hφu : φ u = v) (hφv : φ v = x)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitProfileSum (nu φ) 4 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ orbitBlockDomain D (balanceRule (D := D) B)
        (orbitProfileSum (nu φ) 4)
        (by
          intro d hd
          exact horbit hd)
        (orbitSet φ x) →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
          balanceAt B u v d + balanceAt B v x d = 0 := by
  intro d hd
  rcases hd with ⟨hdD, hBlock⟩
  have hxWin :
      x ∈ balanceRule (D := D) B ⟨orbitProfileSum (nu φ) 4 d, horbit hdD⟩ :=
    hBlock (self_mem_orbitSet φ x)
  have hyWin :
      y ∈ balanceRule (D := D) B ⟨orbitProfileSum (nu φ) 4 d, horbit hdD⟩ := by
    refine hBlock ?_
    exact ⟨1, hφx⟩
  have hxyZero :
      balanceAt B x y (orbitProfileSum (nu φ) 4 d) = 0 :=
    balanceAt_eq_zero_of_two_winners
      (D := D) B hSkew (hd := horbit hdD) hxWin hyWin
  have hTerm1 :
      balanceAt B x y (permuteNProfile (nu φ) d) =
        balanceAt B v x d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB φ v x d
    simpa [hφv, hφx] using hBase
  have hφ2u : (φ ^ 2) u = x := by
    calc
      (φ ^ 2) u = φ (φ u) := by simp [pow_succ']
      _ = x := by simp [hφu, hφv]
  have hφ2v : (φ ^ 2) v = y := by
    calc
      (φ ^ 2) v = φ (φ v) := by simp [pow_succ']
      _ = y := by simp [hφv, hφx]
  have hTerm2 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) =
        balanceAt B u v d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 2) u v d
    simpa [MonoidHom.map_pow, hφ2u, hφ2v] using hBase
  have hφ3z : (φ ^ 3) z = x := by
    calc
      (φ ^ 3) z = φ ((φ ^ 2) z) := by simp [pow_succ']
      _ = φ (φ (φ z)) := by simp [pow_succ']
      _ = x := by simp [hφz, hφu, hφv]
  have hφ3u : (φ ^ 3) u = y := by
    calc
      (φ ^ 3) u = φ ((φ ^ 2) u) := by simp [pow_succ']
      _ = φ (φ (φ u)) := by simp [pow_succ']
      _ = y := by simp [hφu, hφv, hφx]
  have hTerm3 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) =
        balanceAt B z u d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 3) z u d
    simpa [MonoidHom.map_pow, hφ3z, hφ3u] using hBase
  have hφ4y : (φ ^ 4) y = x := by
    calc
      (φ ^ 4) y = φ ((φ ^ 3) y) := by simp [pow_succ']
      _ = φ (φ (φ (φ y))) := by simp [pow_succ']
      _ = x := by simp [hφy, hφz, hφu, hφv]
  have hφ4z : (φ ^ 4) z = y := by
    calc
      (φ ^ 4) z = φ ((φ ^ 3) z) := by simp [pow_succ']
      _ = φ (φ (φ (φ z))) := by simp [pow_succ']
      _ = y := by simp [hφz, hφu, hφv, hφx]
  have hTerm4 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 4) d) =
        balanceAt B y z d := by
    have hBase :=
      balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X))
        (nu := nu) (B := B) hNeutralB (φ ^ 4) y z d
    simpa [MonoidHom.map_pow, hφ4y, hφ4z] using hBase
  have hExpand :
      balanceAt B x y (orbitProfileSum (nu φ) 4 d) =
        balanceAt B x y d +
          balanceAt B x y (permuteNProfile (nu φ) d) +
            balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) +
                balanceAt B x y (permuteNProfile ((nu φ) ^ 4) d) := by
    unfold orbitProfileSum
    simp [Finset.sum_range_succ, balanceAt_add, add_assoc]
  calc
    balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d
        = balanceAt B x y d +
            balanceAt B x y (permuteNProfile (nu φ) d) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) +
                balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) +
                  balanceAt B x y (permuteNProfile ((nu φ) ^ 4) d) := by
            simp [hTerm1, hTerm2, hTerm3, hTerm4, add_assoc, add_left_comm, add_comm]
    _ = balanceAt B x y (orbitProfileSum (nu φ) 4 d) := hExpand.symm
    _ = 0 := hxyZero

lemma c8Fallback_eqC9_on_cycle4_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c4 : C8Cycle4OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) c4 horbit →
        balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d +
          balanceAt B c4.z c4.w d + balanceAt B c4.w c4.x d = 0 := by
  exact c8Fallback_cycle4_sum_on_blockDomain
    (B := B) (hSkew := hSkew) (nu := nu) (hNeutralB := hNeutralB)
    c4.hφx c4.hφy c4.hφz c4.hφw horbit

/-- Case-1 paper equation (C.12) on the designated 4-cycle block-domain.
This is the same 4-term identity as (C.9), written with a cyclic reindexing. -/
lemma c8Fallback_eqC12_on_cycle4_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c4 : C8Cycle4OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) c4 horbit →
        balanceAt B c4.y c4.z d + balanceAt B c4.z c4.w d +
          balanceAt B c4.w c4.x d + balanceAt B c4.x c4.y d = 0 := by
  intro d hd
  have hEqC9 :
      balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d +
        balanceAt B c4.z c4.w d + balanceAt B c4.w c4.x d = 0 :=
    c8Fallback_eqC9_on_cycle4_blockDomain
      (B := B) (hSkew := hSkew) (nu := nu) (hNeutralB := hNeutralB) c4 horbit hd
  simpa [add_assoc, add_left_comm, add_comm] using hEqC9

/-- Hard-core Case-1 step (paper first):
if we already have designated hull-equality for the 4-cycle block-domain, then
Eq. (C.9) follows on all of `D` by hull-lift. -/
theorem c8Fallback_eqC9_on_D_of_designatedHullData
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c4 : C8Cycle4OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D)
    (hHullData :
      ∃ K Kblock : AddSubgroup (ZProfile V),
        IsDivisibleHull (domainImageZ D) K ∧
          IsDivisibleHull
            (domainImageZ (c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) c4 horbit))
            Kblock ∧
          K = Kblock) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d +
        balanceAt B c4.z c4.w d + balanceAt B c4.w c4.x d = 0 := by
  let Dblock : Domain V :=
    c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) c4 horbit
  let c9Weight : V → R := fun v =>
    B.bal c4.x c4.y v + B.bal c4.y c4.z v +
      B.bal c4.z c4.w v + B.bal c4.w c4.x v
  let ψ : ZProfile V →+ R := evalIntHom c9Weight
  rcases hHullData with ⟨K, Kblock, hHullD, hHullBlock, hHullEq⟩
  have hZeroOnBlock : ∀ s, s ∈ domainImageZ Dblock → ψ s = 0 := by
    intro s hs
    rcases hs with ⟨d, hdBlock, rfl⟩
    have hEq :
        balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d +
          balanceAt B c4.z c4.w d + balanceAt B c4.w c4.x d = 0 :=
      c8Fallback_eqC9_on_cycle4_blockDomain
        (D := D) (B := B) (hSkew := hSkew) (nu := nu) (hNeutralB := hNeutralB)
        c4 horbit hdBlock
    have hPsi :
        ψ (toZProfile d) =
          balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d +
            balanceAt B c4.z c4.w d + balanceAt B c4.w c4.x d := by
      change evalIntHom c9Weight (toZProfile d) = _
      rw [evalIntHom_toZProfile]
      unfold c9Weight
      simp [balanceAt, evalNat, add_assoc]
    simpa [hPsi] using hEq
  have hZeroOnD :
      ∀ s, s ∈ domainImageZ D → ψ s = 0 :=
    zero_on_domainImageZ_of_hullEq
      (V := V) (ψ := ψ) (D := D) (Dblock := Dblock)
      (K := K) (Kblock := Kblock)
      hHullD hHullBlock hHullEq hZeroOnBlock
  intro d hdD
  have hzD : toZProfile d ∈ domainImageZ D := ⟨d, hdD, rfl⟩
  have hPsi0 : ψ (toZProfile d) = 0 := hZeroOnD (toZProfile d) hzD
  have hPsi :
      ψ (toZProfile d) =
        balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d +
          balanceAt B c4.z c4.w d + balanceAt B c4.w c4.x d := by
    change evalIntHom c9Weight (toZProfile d) = _
    rw [evalIntHom_toZProfile]
    unfold c9Weight
    simp [balanceAt, evalNat, add_assoc]
  simpa [hPsi] using hPsi0

/-- Infrastructure step for Case 1:
obtain hull-equality on *some* `φ`-orbit block for the designated 4-cycle
permutation data.

This is the exact output of `exists_orbitSet_hull_eq_of_neutral_balance` in the
4-cycle setting; upgrading this existential witness to the designated block
(`c4.x`) is a separate hard step. -/
theorem c8Fallback_exists_hullEq_some_cycle4_orbitBlock
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X]
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (c4 : C8Cycle4OrbitData X)
    (horbit4 : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D) :
    ∃ x0 : X, ∃ K Kx0 : AddSubgroup (ZProfile V),
      IsDivisibleHull (domainImageZ D) K ∧
        IsDivisibleHull
          (domainImageZ
            (orbitBlockDomain D (balanceRule (D := D) B)
              (c8FallbackOrbitMap4 (nu := nu) c4)
              (by
                intro d hd
                exact horbit4 hd)
              (orbitSet c4.φ x0)))
          Kx0 ∧
        K = Kx0 := by
  obtain ⟨K, hHullD⟩ :
      ∃ K : AddSubgroup (ZProfile V), IsDivisibleHull (domainImageZ D) K :=
    exists_divisibleHull (A := ZProfile V) (S := domainImageZ D)
  choose Kx hHullBlocks using
    (fun x : X =>
      exists_divisibleHull
        (A := ZProfile V)
        (S :=
          domainImageZ
            (orbitBlockDomain D (balanceRule (D := D) B)
              (c8FallbackOrbitMap4 (nu := nu) c4)
              (by
                intro d hd
                exact horbit4 hd)
              (orbitSet c4.φ x))))
  rcases exists_orbitSet_hull_eq_of_neutral_balance
      (D := D) (R := R)
      hCone B hR nu hInv hNeutralB hNE
      c4.φ 3 (by simpa using c4.hPow)
      K Kx hHullD
      (by
        intro x
        simpa [c8FallbackOrbitMap4] using hHullBlocks x) with ⟨x0, hHullEq⟩
  exact ⟨x0, K, Kx x0, hHullD, hHullBlocks x0, hHullEq⟩

/-- TODO (Step 2b): reduced 3-term equation target for case 1.
This is intentionally downstream of the paper-style 4-term equations; deriving
it requires combining multiple cycle equations (from different permutations)
plus skew, not just one fixed cycle witness. -/
lemma c8Fallback_eqC10_on_cycle4_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c4 : C8Cycle4OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) c4 horbit →
        balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d =
          balanceAt B c4.x c4.z d := by
  sorry

/-- TODO (Step 2b): reduced 3-term equation target for case 2.
As above, this should be derived after assembling enough paper-style 5-term
equations, rather than from a single fixed cycle witness alone. -/
lemma c8Fallback_eqC16_on_cycle5_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c5 : C8Cycle5OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap5 (nu := nu) c5 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ c8FallbackBlockDomain5 (D := D) (B := B) (nu := nu) c5 horbit →
        balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d =
          balanceAt B c5.x c5.z d := by
  sorry

/-- TODO (Step 2): establish Eq. (C15)-style linear identity on the 5-cycle
fallback block-domain. -/
lemma c8Fallback_eqC15_on_cycle5_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c5 : C8Cycle5OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap5 (nu := nu) c5 d ∈ D) :
    ∀ ⦃d : NProfile V⦄,
      d ∈ c8FallbackBlockDomain5 (D := D) (B := B) (nu := nu) c5 horbit →
        balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d + balanceAt B c5.z c5.u d +
          balanceAt B c5.u c5.v d + balanceAt B c5.v c5.x d = 0 := by
  exact c8Fallback_cycle5_sum_on_blockDomain
    (B := B) (_hSkew) (nu := nu) (_hNeutralB)
    c5.hφx c5.hφy c5.hφz c5.hφu c5.hφv horbit

lemma c8FallbackC10Hom_zero_on_cycle4_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c4 : C8Cycle4OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) c4 d ∈ D) :
    ∀ s,
      s ∈ domainImageZ (c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) c4 horbit) →
        c8FallbackC10Hom (B := B) c4 s = 0 := by
  intro s hs
  rcases hs with ⟨d, hd, rfl⟩
  have hEq :
      balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d =
        balanceAt B c4.x c4.z d :=
    c8Fallback_eqC10_on_cycle4_blockDomain
      (B := B) (nu := nu) hSkew hNeutralB c4 horbit hd
  calc
    c8FallbackC10Hom (B := B) c4 (toZProfile d)
        = balanceAt B c4.x c4.y d + balanceAt B c4.y c4.z d - balanceAt B c4.x c4.z d := by
            exact c8FallbackC10Hom_toZProfile (B := B) c4 d
    _ = 0 := sub_eq_zero.mpr hEq

lemma c8FallbackC16Hom_zero_on_cycle5_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c5 : C8Cycle5OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap5 (nu := nu) c5 d ∈ D) :
    ∀ s,
      s ∈ domainImageZ (c8FallbackBlockDomain5 (D := D) (B := B) (nu := nu) c5 horbit) →
        c8FallbackC16Hom (B := B) c5 s = 0 := by
  intro s hs
  rcases hs with ⟨d, hd, rfl⟩
  have hEq :
      balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d =
        balanceAt B c5.x c5.z d :=
    c8Fallback_eqC16_on_cycle5_blockDomain
      (B := B) (nu := nu) hSkew hNeutralB c5 horbit hd
  calc
    c8FallbackC16Hom (B := B) c5 (toZProfile d)
        = balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d - balanceAt B c5.x c5.z d := by
            exact c8FallbackC16Hom_toZProfile (B := B) c5 d
    _ = 0 := sub_eq_zero.mpr hEq

lemma c8FallbackC15Hom_zero_on_cycle5_blockDomain
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (c5 : C8Cycle5OrbitData X)
    (horbit : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap5 (nu := nu) c5 d ∈ D) :
    ∀ s,
      s ∈ domainImageZ (c8FallbackBlockDomain5 (D := D) (B := B) (nu := nu) c5 horbit) →
        c8FallbackC15Hom (B := B) c5 s = 0 := by
  intro s hs
  rcases hs with ⟨d, hd, rfl⟩
  have hEq :
      balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d + balanceAt B c5.z c5.u d +
        balanceAt B c5.u c5.v d + balanceAt B c5.v c5.x d = 0 :=
    c8Fallback_eqC15_on_cycle5_blockDomain
      (B := B) (nu := nu) hSkew hNeutralB c5 horbit hd
  calc
    c8FallbackC15Hom (B := B) c5 (toZProfile d)
        = balanceAt B c5.x c5.y d + balanceAt B c5.y c5.z d + balanceAt B c5.z c5.u d +
            balanceAt B c5.u c5.v d + balanceAt B c5.v c5.x d := by
              exact c8FallbackC15Hom_toZProfile (B := B) c5 d
    _ = 0 := hEq

lemma c8Fallback_equationPack4_of_cycleSum
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hCycle : C8CycleSumHypothesis (D := D) (B := B)) :
    Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) := by
  rcases hCycle with ⟨x, y, z, hxy, hyz, hzx, hSum⟩
  have hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d = balanceAt B x z d := by
    exact c8Fallback_eqC10_of_cycleSum
      (R := R) (D := D) (B := B) hSkew hSum
  refine ⟨⟨x, y, z, y, hxy, hyz, hzx, hyz.symm, hxy.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d hd
    calc
      balanceAt B x y d + balanceAt B y z d + balanceAt B z y d + balanceAt B y x d
          = balanceAt B x y d + balanceAt B y x d + (balanceAt B y z d + balanceAt B z y d) := by
              simp [add_assoc, add_left_comm, add_comm]
      _ = balanceAt B x y d + (-balanceAt B x y d) + (balanceAt B y z d + balanceAt B z y d) := by
              simp [hSkew y x d]
      _ = balanceAt B x y d + (-balanceAt B x y d) + (balanceAt B y z d + (-balanceAt B y z d)) := by
              simp [hSkew z y d]
      _ = 0 := by simp
  · intro d hd
    exact hC10 hd
  · intro d hd
    calc
      balanceAt B y z d + balanceAt B z y d
          = balanceAt B y z d + (-balanceAt B y z d) := by
              simp [hSkew z y d]
      _ = 0 := by simp
      _ = balanceAt B y y d := by
          symm
          exact c8Fallback_balanceAt_diag_eq_zero_of_skew
            (R := R) (B := B) hSkew y d
  · intro d hd
    calc
      balanceAt B z y d + balanceAt B y x d
          = (-balanceAt B y z d) + (-balanceAt B x y d) := by
              simp [hSkew z y d, hSkew y x d]
      _ = -(balanceAt B x y d + balanceAt B y z d) := by
              simp
      _ = -balanceAt B x z d := by simp [hC10 hd]
      _ = balanceAt B z x d := by simp [hSkew z x d]
  · intro d hd
    calc
      balanceAt B y x d + balanceAt B x y d
          = -balanceAt B x y d + balanceAt B x y d := by
              simp [hSkew y x d]
      _ = 0 := by simp
      _ = balanceAt B y y d := by
          symm
          exact c8Fallback_balanceAt_diag_eq_zero_of_skew
            (R := R) (B := B) hSkew y d
  · intro d hd
    calc
      balanceAt B x z d + balanceAt B z y d
          = balanceAt B x z d + (-balanceAt B y z d) := by simp [hSkew z y d]
      _ = (balanceAt B x y d + balanceAt B y z d) + (-balanceAt B y z d) := by
            simp [hC10 hd]
      _ = balanceAt B x y d := by simp [add_assoc]

/-- TODO: convert 4-cycle fallback equations into triangle cycle-sum law. -/
theorem c8CycleSumHypothesis_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hPack4 with ⟨x, y, z, w, hxy, hyz, hzx, _hzw, _hwx, hC9, hC10, _hC11, hC12, _hC13, _hC14⟩
  refine ⟨x, y, z, hxy, hyz, hzx, ?_⟩
  intro d hd
  have h9 :
      (balanceAt B x y d + balanceAt B y z d) +
        (balanceAt B z w d + balanceAt B w x d) = 0 := by
    simpa [add_assoc] using hC9 hd
  have hxzzx : balanceAt B x z d + balanceAt B z x d = 0 := by
    calc
      balanceAt B x z d + balanceAt B z x d
          = (balanceAt B x y d + balanceAt B y z d) +
              (balanceAt B z w d + balanceAt B w x d) := by
                simp [hC10 hd, hC12 hd]
      _ = 0 := h9
  calc
    balanceAt B x y d + balanceAt B y z d + balanceAt B z x d
        = balanceAt B x z d + balanceAt B z x d := by
            simp [hC10 hd]
    _ = 0 := hxzzx

/-- TODO: convert 5-cycle fallback equations into triangle cycle-sum law. -/
theorem c8CycleSumHypothesis_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hPack5 with
    ⟨x, y, z, u, v, hxy, hyz, hzx, _hzu, _huv, _hvx,
      hC15, hC16, _hC17, hC18, _hC19, hC20⟩
  refine ⟨x, y, z, hxy, hyz, hzx, ?_⟩
  intro d hd
  have h15 :
      (balanceAt B x y d + balanceAt B y z d) +
          ((balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d) = 0 := by
    simpa [add_assoc] using hC15 hd
  have hzx_repr :
      balanceAt B z x d =
        (balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d := by
    calc
      balanceAt B z x d = balanceAt B z v d + balanceAt B v x d := (hC20 hd).symm
      _ = (balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d := by
            simp [hC18 hd]
  have hxzzx : balanceAt B x z d + balanceAt B z x d = 0 := by
    calc
      balanceAt B x z d + balanceAt B z x d
          = (balanceAt B x y d + balanceAt B y z d) +
              ((balanceAt B z u d + balanceAt B u v d) + balanceAt B v x d) := by
                simp [hC16 hd, hzx_repr, add_assoc]
      _ = 0 := h15
  calc
    balanceAt B x y d + balanceAt B y z d + balanceAt B z x d
        = balanceAt B x z d + balanceAt B z x d := by
            simp [hC16 hd]
    _ = 0 := hxzzx

theorem c8CycleSumHypothesis_of_equationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hPack : C8FallbackEquationPack (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hPack with hPack4 | hPack5
  · rcases hPack4 with ⟨hPack4⟩
    exact c8CycleSumHypothesis_of_equationPack4
      (D := D) (B := B) hPack4
  · rcases hPack5 with ⟨hPack5⟩
    exact c8CycleSumHypothesis_of_equationPack5
      (D := D) (B := B) hPack5

theorem c8Fallback_fourFiveCycleBranch_of_equationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hPack : C8FallbackEquationPack (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact c8CycleSumHypothesis_of_equationPack (D := D) (B := B) hPack

/-- TODO: build either a 4-cycle or 5-cycle fallback package in case `% 3 = 1`. -/
theorem c8Fallback_equationPack45_of_case1
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) ∨
      Nonempty (C8FallbackEquationPack5 (D := D) (B := B)) := by
  rcases c8Cycle4OrbitData_of_case1 (X := X) hCardGtTwo hCase1 with ⟨d4⟩
  have horbit4 : ∀ {d : NProfile V}, d ∈ D →
      c8FallbackOrbitMap4 (nu := nu) d4 d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv d4.φ hd 3
  /- Hardest Case-1 step (paper-faithful):
     produce designated hull-equality for the `d4` block so (C.9) lifts to `D`.
     All other Case-1 equations are derived downstream from this. -/
  have hHullData4 :
      ∃ K Kblock : AddSubgroup (ZProfile V),
        IsDivisibleHull (domainImageZ D) K ∧
          IsDivisibleHull
            (domainImageZ (c8FallbackBlockDomain4 (D := D) (B := B) (nu := nu) d4 horbit4))
            Kblock ∧
          K = Kblock := by
    have hNE : NonemptyOnDomain D (balanceRule (D := D) B) := by
      /- TODO (hard): this is the same Stage-F nonemptiness gap as in
      `C8Bridge` step 2.  It is not derivable from current assumptions alone
      (`PerfectOn` is vacuous when winners are empty), so we likely need either:
      (i) an explicit `NonemptyOnDomain` hypothesis, or
      (ii) an upstream theorem supplying it in the paper pipeline. -/
      sorry
    rcases c8Fallback_exists_hullEq_some_cycle4_orbitBlock
        (nu := nu) (R := R) (D := D)
        hCone B hR hInv hNeutralB hNE d4 horbit4 with
        ⟨x0, K, Kx0, hHullD, hHullBlock0, hHullEq0⟩
    have hx0 : x0 = d4.x := by
      /- TODO (hard, paper-structure gap):
      the C.7 consequence currently gives `∃ x0, K = Kx x0`.
      We still need the Claim-C.8.4 style argument that upgrades this
      existential witness to the designated Case-1 block (`x0 = d4.x`). -/
      sorry
    subst hx0
    exact ⟨K, Kx0, hHullD, by simpa [c8FallbackBlockDomain4] using hHullBlock0, hHullEq0⟩
  have hEqC9 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.x d4.y d + balanceAt B d4.y d4.z d +
          balanceAt B d4.z d4.w d + balanceAt B d4.w d4.x d = 0 := by
    exact c8Fallback_eqC9_on_D_of_designatedHullData
      (D := D) (B := B) (hSkew := hSkew) (nu := nu) (hNeutralB := hNeutralB)
      d4 horbit4 hHullData4
  have hyw : d4.y ≠ d4.w := by
    intro hyw
    have hzxEq : d4.z = d4.x := by
      calc
        d4.z = d4.φ d4.y := by symm; exact d4.hφy
        _ = d4.φ d4.w := by simp [hyw]
        _ = d4.x := d4.hφw
    exact d4.hzx hzxEq
  have hEqC10p :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.x d4.y d + balanceAt B d4.y d4.w d +
          balanceAt B d4.w d4.z d + balanceAt B d4.z d4.x d = 0 := by
    exact c8Fallback_eqC10p_of_eqC9_swap
      (nu := nu) (R := R) (D := D) (B := B) hInv hNeutralB
      d4.hzx.symm d4.hwx.symm d4.hyz hyw hEqC9
  have hEqC11p :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.y d4.z d + balanceAt B d4.z d4.x d +
          balanceAt B d4.x d4.w d + balanceAt B d4.w d4.y d = 0 := by
    exact c8Fallback_eqC11p_of_eqC10p_rotate
      (nu := nu) (R := R) (D := D) (B := B)
      hInv hNeutralB d4.hφx d4.hφy d4.hφz d4.hφw hEqC10p
  have hEqC12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.y d4.z d + balanceAt B d4.z d4.w d +
          balanceAt B d4.w d4.x d + balanceAt B d4.x d4.y d = 0 := by
    intro d hd
    simpa [add_assoc, add_left_comm, add_comm] using hEqC9 hd
  have hEqC13 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.z d4.x d + balanceAt B d4.x d4.y d +
          balanceAt B d4.y d4.w d + balanceAt B d4.w d4.z d = 0 := by
    intro d hd
    simpa [add_assoc, add_left_comm, add_comm] using hEqC10p hd
  have hEqC14 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.z d4.x d + balanceAt B d4.x d4.w d +
          balanceAt B d4.w d4.y d + balanceAt B d4.y d4.z d = 0 := by
    intro d hd
    simpa [add_assoc, add_left_comm, add_comm] using hEqC11p hd
  have hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.x d4.y d + balanceAt B d4.y d4.z d =
          balanceAt B d4.x d4.z d := by
    exact c8Fallback_eqC10_of_case1_sixEquations
      (R := R) (D := D) (B := B) hSkew
      hEqC9 hEqC10p hEqC11p hEqC12 hEqC13 hEqC14
  have hC11 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.y d4.z d + balanceAt B d4.z d4.w d =
          balanceAt B d4.y d4.w d := by
    exact c8Fallback_eqC11_of_eqC10_rotate
      (nu := nu) (R := R) (D := D) (B := B)
      hInv hNeutralB d4.hφx d4.hφy d4.hφz d4.hφw hC10
  have hC12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.z d4.w d + balanceAt B d4.w d4.x d =
          balanceAt B d4.z d4.x d := by
    exact c8Fallback_eqC12_of_eqC10_rotate
      (nu := nu) (R := R) (D := D) (B := B)
      hInv hNeutralB d4.hφx d4.hφy d4.hφz d4.hφw hC10
  have hC13 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.w d4.x d + balanceAt B d4.x d4.y d =
          balanceAt B d4.w d4.y d := by
    exact c8Fallback_eqC13_of_eqC10_eqC11_eqC12
      (R := R) (D := D) (B := B) hSkew hC10 hC11 hC12
  refine Or.inl ?_
  refine ⟨{ x := d4.x
            y := d4.y
            z := d4.z
            w := d4.w
            hxy := d4.hxy
            hyz := d4.hyz
            hzx := d4.hzx
            hzw := d4.hzw
            hwx := d4.hwx
            eqC9 := c8Fallback_eqC9_of_eqC10_eqC12
              (R := R) (D := D) (B := B) hSkew hC10 hC12
            eqC10 := hC10
            eqC11 := hC11
            eqC12 := hC12
            eqC13 := hC13
            eqC14 := c8Fallback_eqC14_of_eqC12
              (R := R) (D := D) (B := B) hSkew hC12 }⟩

/-- TODO: build either a 4-cycle or 5-cycle fallback package in case `% 3 = 2`. -/
theorem c8Fallback_equationPack45_of_case2
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) ∨
      Nonempty (C8FallbackEquationPack5 (D := D) (B := B)) := by
  rcases c8Cycle5OrbitData_of_case2 (X := X) hCardGtTwo hCase2 with ⟨d5⟩
  have hC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d5.x d5.y d + balanceAt B d5.y d5.z d =
          balanceAt B d5.x d5.z d := by
    sorry
  have hC17 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d5.y d5.z d + balanceAt B d5.z d5.u d =
          balanceAt B d5.y d5.u d := by
    exact c8Fallback_eqC17_of_eqC16_rotate
      (nu := nu) (R := R) (D := D) (B := B)
      hInv hNeutralB d5.hφx d5.hφy d5.hφz d5.hφu d5.hφv hC16
  have hC18 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d5.z d5.u d + balanceAt B d5.u d5.v d =
          balanceAt B d5.z d5.v d := by
    exact c8Fallback_eqC18_of_eqC16_rotate
      (nu := nu) (R := R) (D := D) (B := B)
      hInv hNeutralB d5.hφx d5.hφy d5.hφz d5.hφu d5.hφv hC16
  have hC19 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d5.u d5.v d + balanceAt B d5.v d5.x d =
          balanceAt B d5.u d5.x d := by
    exact c8Fallback_eqC19_of_eqC16_rotate
      (nu := nu) (R := R) (D := D) (B := B)
      hInv hNeutralB d5.hφx d5.hφy d5.hφz d5.hφu d5.hφv hC16
  have hC15 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d5.x d5.y d + balanceAt B d5.y d5.z d + balanceAt B d5.z d5.u d +
          balanceAt B d5.u d5.v d + balanceAt B d5.v d5.x d = 0 := by
    sorry
  have hC20 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d5.z d5.v d + balanceAt B d5.v d5.x d =
          balanceAt B d5.z d5.x d := by
    exact c8Fallback_eqC20_of_eqC15_eqC16_eqC18
      (R := R) (D := D) (B := B) hSkew hC15 hC16 hC18
  refine Or.inr ?_
  refine ⟨{ x := d5.x
            y := d5.y
            z := d5.z
            u := d5.u
            v := d5.v
            hxy := d5.hxy
            hyz := d5.hyz
            hzx := d5.hzx
            hzu := d5.hzu
            huv := d5.huv
            hvx := d5.hvx
            eqC15 := hC15
            eqC16 := hC16
            eqC17 := hC17
            eqC18 := hC18
            eqC19 := hC19
            eqC20 := hC20 }⟩

/-- TODO: derive fallback equation package from case `% 3 = 1` assumptions. -/
theorem c8Fallback_equationPack_of_case1
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    C8FallbackEquationPack (D := D) (B := B) := by
  exact c8Fallback_equationPack45_of_case1
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase1

/-- TODO: derive fallback equation package from case `% 3 = 2` assumptions. -/
theorem c8Fallback_equationPack_of_case2
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    C8FallbackEquationPack (D := D) (B := B) := by
  exact c8Fallback_equationPack45_of_case2
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase2

/-- Derive triangle cycle-sum from case `% 3 = 1` via fallback package generation
and equation-pack conversion. -/
theorem c8Fallback_cycleSumHypothesis_of_case1
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  exact c8CycleSumHypothesis_of_equationPack (D := D) (B := B)
    (c8Fallback_equationPack_of_case1
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase1)

theorem c8Fallback_fourFiveCycleBranch_of_case1
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact c8Fallback_fourFiveCycleBranch_of_equationPack
    (D := D) (B := B)
    (c8Fallback_equationPack_of_case1
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase1)

theorem c8Fallback_fourFiveCycleBranch_of_case2
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact c8Fallback_fourFiveCycleBranch_of_equationPack
    (D := D) (B := B)
    (c8Fallback_equationPack_of_case2
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase2)

theorem c8Fallback_branchSplit_of_case1
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  exact Or.inr
    (c8Fallback_fourFiveCycleBranch_of_case1
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase1)

theorem c8Fallback_branchSplit_of_case2
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  exact Or.inr
    (c8Fallback_fourFiveCycleBranch_of_case2
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hCardGtTwo hCase2)

end C8Fallback

end Pivato
