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
    intro d hd
    have hsum0 :
        (balanceAt B x y d + balanceAt B y z d) + balanceAt B z x d = 0 := by
      simpa [add_assoc] using hSum hd
    have hneg :
        balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d :=
      eq_neg_of_add_eq_zero_left hsum0
    calc
      balanceAt B x y d + balanceAt B y z d = -balanceAt B z x d := hneg
      _ = balanceAt B x z d := by simp [hSkew z x d]
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
  have hC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B d4.x d4.y d + balanceAt B d4.y d4.z d =
          balanceAt B d4.x d4.z d := by
    sorry
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
