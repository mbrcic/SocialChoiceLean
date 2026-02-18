import Pivato.Theorem2.C8Branch
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# C.8 orbit/case infrastructure

This file isolates reusable combinatorial/permutation infrastructure for the
C.8 bridge:
- orbit-cycle data records (length 3/4/5);
- small transport lemmas into `orbitSet`.
-/

namespace Pivato

section C8OrbitCases

universe uX

variable {X : Type uX}

/-- Canonical 3-cycle permutation on `(x,y,z)`:
`x ↦ y`, `y ↦ z`, `z ↦ x`, identity elsewhere. -/
def c8Cycle3Perm [DecidableEq X] (x y z : X) : Equiv.Perm X :=
  Equiv.swap x y * Equiv.swap y z

lemma c8Cycle3Perm_apply_x
    [DecidableEq X]
    {x y z : X}
    (hxy : x ≠ y) (hzx : z ≠ x) :
    c8Cycle3Perm x y z x = y := by
  unfold c8Cycle3Perm
  have hxz : x ≠ z := by
    intro hxz
    exact hzx hxz.symm
  have hinner : Equiv.swap y z x = x :=
    Equiv.swap_apply_of_ne_of_ne hxy hxz
  calc
    (Equiv.swap x y * Equiv.swap y z) x = (Equiv.swap x y) ((Equiv.swap y z) x) := rfl
    _ = (Equiv.swap x y) x := by simp [hinner]
    _ = y := by simp [Equiv.swap_apply_left]

lemma c8Cycle3Perm_apply_y
    [DecidableEq X]
    {x y z : X}
    (hyz : y ≠ z) (hzx : z ≠ x) :
    c8Cycle3Perm x y z y = z := by
  unfold c8Cycle3Perm
  calc
    (Equiv.swap x y * Equiv.swap y z) y = (Equiv.swap x y) ((Equiv.swap y z) y) := rfl
    _ = (Equiv.swap x y) z := by simp [Equiv.swap_apply_left]
    _ = z := by
      have hzy : z ≠ y := hyz.symm
      exact Equiv.swap_apply_of_ne_of_ne hzx hzy

lemma c8Cycle3Perm_apply_z
    [DecidableEq X]
    {x y z : X} :
    c8Cycle3Perm x y z z = x := by
  unfold c8Cycle3Perm
  calc
    (Equiv.swap x y * Equiv.swap y z) z = (Equiv.swap x y) ((Equiv.swap y z) z) := rfl
    _ = (Equiv.swap x y) y := by simp [Equiv.swap_apply_right]
    _ = x := by simp [Equiv.swap_apply_right]

lemma c8Cycle3Perm_apply_of_ne
    [DecidableEq X]
    {x y z t : X}
    (htx : t ≠ x) (hty : t ≠ y) (htz : t ≠ z) :
    c8Cycle3Perm x y z t = t := by
  unfold c8Cycle3Perm
  have hinner : Equiv.swap y z t = t :=
    Equiv.swap_apply_of_ne_of_ne hty htz
  calc
    (Equiv.swap x y * Equiv.swap y z) t = (Equiv.swap x y) ((Equiv.swap y z) t) := rfl
    _ = (Equiv.swap x y) t := by simp [hinner]
    _ = t := by exact Equiv.swap_apply_of_ne_of_ne htx hty

lemma c8Cycle3Perm_pow_three
    [DecidableEq X]
    {x y z : X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    (c8Cycle3Perm x y z) ^ 3 = 1 := by
  ext t
  by_cases htx : t = x
  · subst t
    calc
      ((c8Cycle3Perm x y z) ^ 3) x
          = (c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) x)) := by
              simp [pow_succ']
      _ = (c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) y) := by
            simp [c8Cycle3Perm_apply_x, hxy, hzx]
      _ = (c8Cycle3Perm x y z) z := by simp [c8Cycle3Perm_apply_y, hyz, hzx]
      _ = x := by simp [c8Cycle3Perm_apply_z]
  · by_cases hty : t = y
    · subst t
      calc
        ((c8Cycle3Perm x y z) ^ 3) y
            = (c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) y)) := by
                simp [pow_succ']
        _ = (c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) z) := by
              simp [c8Cycle3Perm_apply_y, hyz, hzx]
        _ = (c8Cycle3Perm x y z) x := by simp [c8Cycle3Perm_apply_z]
        _ = y := by simp [c8Cycle3Perm_apply_x, hxy, hzx]
    · by_cases htz : t = z
      · subst t
        calc
          ((c8Cycle3Perm x y z) ^ 3) z
              = (c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) z)) := by
                  simp [pow_succ']
          _ = (c8Cycle3Perm x y z) ((c8Cycle3Perm x y z) x) := by
                simp [c8Cycle3Perm_apply_z]
          _ = (c8Cycle3Perm x y z) y := by
                simp [c8Cycle3Perm_apply_x, hxy, hzx]
          _ = z := by simp [c8Cycle3Perm_apply_y, hyz, hzx]
      · have hfix : c8Cycle3Perm x y z t = t :=
          c8Cycle3Perm_apply_of_ne (x := x) (y := y) (z := z) (t := t)
            (by simpa using htx) (by simpa using hty) (by simpa using htz)
        have hpowfix : ∀ n : ℕ, ((c8Cycle3Perm x y z) ^ n) t = t := by
          intro n
          induction n with
          | zero => simp
          | succ n ihn =>
              calc
                ((c8Cycle3Perm x y z) ^ (n + 1)) t
                    = c8Cycle3Perm x y z (((c8Cycle3Perm x y z) ^ n) t) := by
                        simp [pow_succ']
                _ = c8Cycle3Perm x y z t := by simp [ihn]
                _ = t := hfix
        simpa using hpowfix 3

/-- Orbit-data package for the 3-cycle branch. -/
structure C8Cycle3OrbitData (X : Type uX) where
  φ : Equiv.Perm X
  hPow : φ ^ 3 = 1
  x : X
  y : X
  z : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hφx : φ x = z
  hφy : φ y = x
  hφz : φ z = y

noncomputable def c8Cycle3OrbitData_of_distinct
    [DecidableEq X]
    {x y z : X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    C8Cycle3OrbitData X where
  φ := c8Cycle3Perm x z y
  hPow := by
    simpa using
      c8Cycle3Perm_pow_three (x := x) (y := z) (z := y)
        hzx.symm hyz.symm hxy.symm
  x := x
  y := y
  z := z
  hxy := hxy
  hyz := hyz
  hzx := hzx
  hφx := by
    simpa using
      c8Cycle3Perm_apply_x (x := x) (y := z) (z := y) hzx.symm hxy.symm
  hφy := by
    simpa using c8Cycle3Perm_apply_z (x := x) (y := z) (z := y)
  hφz := by
    simpa using c8Cycle3Perm_apply_y (x := x) (y := z) (z := y) hyz.symm hxy.symm

abbrev C8Fin3 := Fin 3

def c8Fin3Cycle : Equiv.Perm C8Fin3 :=
  c8Cycle3Perm (0 : C8Fin3) (1 : C8Fin3) (2 : C8Fin3)

lemma c8Fin3Cycle_pow_three :
    (c8Fin3Cycle ^ 3) = 1 := by
  apply Equiv.Perm.ext
  intro i
  fin_cases i <;> decide

lemma c8Fin3Cycle_no_fixed (i : C8Fin3) :
    c8Fin3Cycle i ≠ i := by
  fin_cases i <;> decide

def c8ProdThreePerm (m : ℕ) : Equiv.Perm (Fin m × C8Fin3) :=
  Equiv.prodCongr (Equiv.refl (Fin m)) c8Fin3Cycle

lemma c8ProdThreePerm_pow_three (m : ℕ) :
    (c8ProdThreePerm m) ^ 3 = 1 := by
  apply Equiv.Perm.ext
  intro p
  rcases p with ⟨a, b⟩
  have h3 : c8Fin3Cycle (c8Fin3Cycle (c8Fin3Cycle b)) = b := by
    have hpow : (c8Fin3Cycle ^ 3) b = b := by
      simpa using congrArg (fun q : Equiv.Perm C8Fin3 => q b) c8Fin3Cycle_pow_three
    simpa [pow_succ'] using hpow
  simp [c8ProdThreePerm, Equiv.prodCongr_apply, h3, pow_succ']

lemma c8ProdThreePerm_no_fixed (m : ℕ) (p : Fin m × C8Fin3) :
    c8ProdThreePerm m p ≠ p := by
  rcases p with ⟨a, b⟩
  simp [c8ProdThreePerm, Equiv.prodCongr_apply, c8Fin3Cycle_no_fixed]

lemma c8PowThree_transport
    {A B : Type*} (e : A ≃ B) (φ : Equiv.Perm B)
    (hPow : φ ^ 3 = 1) :
    ((e.trans φ).trans e.symm) ^ 3 = 1 := by
  apply Equiv.Perm.ext
  intro a
  apply e.injective
  have hPowAt : (φ ^ 3) (e a) = e a := by
    simpa using congrArg (fun q : Equiv.Perm B => q (e a)) hPow
  simpa [pow_succ'] using hPowAt

lemma c8NoFixed_transport
    {A B : Type*} (e : A ≃ B) (φ : Equiv.Perm B)
    (hNoFix : ∀ b : B, φ b ≠ b) :
    ∀ a : A, ((e.trans φ).trans e.symm) a ≠ a := by
  intro a hFix
  have hFix' : φ (e a) = e a := by
    simpa using congrArg e hFix
  exact hNoFix (e a) hFix'

noncomputable def c8Case0PermOfCardEq
    [Fintype X]
    (m : ℕ) (hCard : Fintype.card X = m * 3) :
    Equiv.Perm X := by
  let eFin : X ≃ Fin (m * 3) := Fintype.equivFinOfCardEq hCard
  let eProd : X ≃ Fin m × C8Fin3 := eFin.trans finProdFinEquiv.symm
  exact (eProd.trans (c8ProdThreePerm m)).trans eProd.symm

lemma c8Case0PermOfCardEq_pow_three
    [Fintype X]
    (m : ℕ) (hCard : Fintype.card X = m * 3) :
    (c8Case0PermOfCardEq (X := X) m hCard) ^ 3 = 1 := by
  classical
  let eFin : X ≃ Fin (m * 3) := Fintype.equivFinOfCardEq hCard
  let eProd : X ≃ Fin m × C8Fin3 := eFin.trans finProdFinEquiv.symm
  simpa [c8Case0PermOfCardEq, eProd] using
    c8PowThree_transport eProd (c8ProdThreePerm m) (c8ProdThreePerm_pow_three m)

lemma c8Case0PermOfCardEq_no_fixed
    [Fintype X]
    (m : ℕ) (hCard : Fintype.card X = m * 3) :
    ∀ x : X, c8Case0PermOfCardEq (X := X) m hCard x ≠ x := by
  classical
  let eFin : X ≃ Fin (m * 3) := Fintype.equivFinOfCardEq hCard
  let eProd : X ≃ Fin m × C8Fin3 := eFin.trans finProdFinEquiv.symm
  simpa [c8Case0PermOfCardEq, eProd] using
    c8NoFixed_transport eProd (c8ProdThreePerm m) (c8ProdThreePerm_no_fixed m)

theorem c8ExistsPerm_pow_three_no_fixed_of_card_mod_three_eq_zero
    [Fintype X]
    (hCase0 : Fintype.card X % 3 = 0) :
    ∃ φ : Equiv.Perm X, φ ^ 3 = 1 ∧ ∀ x : X, φ x ≠ x := by
  obtain ⟨m, hm3⟩ : ∃ m : ℕ, Fintype.card X = 3 * m := by
    have hDvd : 3 ∣ Fintype.card X := (Nat.dvd_iff_mod_eq_zero).2 hCase0
    rcases hDvd with ⟨m, hm⟩
    exact ⟨m, hm⟩
  let hm : Fintype.card X = m * 3 := by
    simpa [Nat.mul_comm] using hm3
  refine
    ⟨c8Case0PermOfCardEq (X := X) m hm,
      c8Case0PermOfCardEq_pow_three (X := X) m hm,
      c8Case0PermOfCardEq_no_fixed (X := X) m hm⟩

noncomputable def c8Cycle3OrbitData_of_powThree_noFixed
    (φ : Equiv.Perm X)
    (hPow : φ ^ 3 = 1)
    (hNoFix : ∀ x : X, φ x ≠ x)
    (x : X) :
    C8Cycle3OrbitData X where
  φ := φ
  hPow := hPow
  x := x
  y := (φ ^ 2) x
  z := φ x
  hxy := by
    intro hxy
    have hφy : φ ((φ ^ 2) x) = x := by
      have hPowAt : (φ ^ 3) x = x := by
        simpa using congrArg (fun q : Equiv.Perm X => q x) hPow
      simpa [pow_succ'] using hPowAt
    have hFix : φ x = x := by
      calc
        φ x = φ ((φ ^ 2) x) := by exact congrArg φ hxy
        _ = x := hφy
    exact (hNoFix x) hFix
  hyz := by
    intro hyz
    have hφy : φ ((φ ^ 2) x) = x := by
      have hPowAt : (φ ^ 3) x = x := by
        simpa using congrArg (fun q : Equiv.Perm X => q x) hPow
      simpa [pow_succ'] using hPowAt
    have hφz : φ (φ x) = (φ ^ 2) x := by
      simp [pow_succ']
    have hxEqY : x = (φ ^ 2) x := by
      calc
        x = φ ((φ ^ 2) x) := hφy.symm
        _ = φ (φ x) := by simp [hyz]
        _ = (φ ^ 2) x := hφz
    exact (by
      have hxy : x ≠ (φ ^ 2) x := by
        intro hxy
        have hφy' : φ ((φ ^ 2) x) = x := by
          have hPowAt : (φ ^ 3) x = x := by
            simpa using congrArg (fun q : Equiv.Perm X => q x) hPow
          simpa [pow_succ'] using hPowAt
        have hFix : φ x = x := by
          calc
            φ x = φ ((φ ^ 2) x) := by exact congrArg φ hxy
            _ = x := hφy'
        exact (hNoFix x) hFix
      exact hxy hxEqY)
  hzx := by
    simpa using hNoFix x
  hφx := rfl
  hφy := by
    have hPowAt : (φ ^ 3) x = x := by
      simpa using congrArg (fun q : Equiv.Perm X => q x) hPow
    simpa [pow_succ'] using hPowAt
  hφz := by
    simp [pow_succ']

abbrev C8Fin4 := Fin 4
abbrev C8Fin5 := Fin 5

def c8Fin4Cycle : Equiv.Perm C8Fin4 :=
  Equiv.swap (0 : C8Fin4) (1 : C8Fin4) *
    Equiv.swap (1 : C8Fin4) (2 : C8Fin4) *
      Equiv.swap (2 : C8Fin4) (3 : C8Fin4)

def c8Fin5Cycle : Equiv.Perm C8Fin5 :=
  Equiv.swap (0 : C8Fin5) (1 : C8Fin5) *
    Equiv.swap (1 : C8Fin5) (2 : C8Fin5) *
      Equiv.swap (2 : C8Fin5) (3 : C8Fin5) *
        Equiv.swap (3 : C8Fin5) (4 : C8Fin5)

lemma c8Fin4Cycle_pow_four :
    (c8Fin4Cycle ^ 4) = 1 := by
  apply Equiv.Perm.ext
  intro i
  fin_cases i <;> decide

lemma c8Fin5Cycle_pow_five :
    (c8Fin5Cycle ^ 5) = 1 := by
  apply Equiv.Perm.ext
  intro i
  fin_cases i <;> decide

lemma c8Fin4Cycle_apply0 :
    c8Fin4Cycle 0 = (1 : C8Fin4) := by decide

lemma c8Fin4Cycle_apply1 :
    c8Fin4Cycle 1 = (2 : C8Fin4) := by decide

lemma c8Fin4Cycle_apply2 :
    c8Fin4Cycle 2 = (3 : C8Fin4) := by decide

lemma c8Fin4Cycle_apply3 :
    c8Fin4Cycle 3 = (0 : C8Fin4) := by decide

lemma c8Fin4Cycle_no_fixed (i : C8Fin4) :
    c8Fin4Cycle i ≠ i := by
  fin_cases i <;> decide

lemma c8Fin5Cycle_apply0 :
    c8Fin5Cycle 0 = (1 : C8Fin5) := by decide

lemma c8Fin5Cycle_apply1 :
    c8Fin5Cycle 1 = (2 : C8Fin5) := by decide

lemma c8Fin5Cycle_apply2 :
    c8Fin5Cycle 2 = (3 : C8Fin5) := by decide

lemma c8Fin5Cycle_apply3 :
    c8Fin5Cycle 3 = (4 : C8Fin5) := by decide

lemma c8Fin5Cycle_apply4 :
    c8Fin5Cycle 4 = (0 : C8Fin5) := by decide

lemma c8Fin5Cycle_no_fixed (i : C8Fin5) :
    c8Fin5Cycle i ≠ i := by
  fin_cases i <;> decide

lemma c8ProdThreePerm_pow_twelve (m : ℕ) :
    (c8ProdThreePerm m) ^ 12 = 1 := by
  calc
    (c8ProdThreePerm m) ^ 12 = ((c8ProdThreePerm m) ^ 3) ^ 4 := by
      have h12 : (12 : ℕ) = 3 * 4 := by decide
      simpa [h12] using (pow_mul (c8ProdThreePerm m) 3 4)
    _ = 1 := by
      simp [c8ProdThreePerm_pow_three]

lemma c8ProdThreePerm_pow_fifteen (m : ℕ) :
    (c8ProdThreePerm m) ^ 15 = 1 := by
  calc
    (c8ProdThreePerm m) ^ 15 = ((c8ProdThreePerm m) ^ 3) ^ 5 := by
      have h15 : (15 : ℕ) = 3 * 5 := by decide
      simpa [h15] using (pow_mul (c8ProdThreePerm m) 3 5)
    _ = 1 := by
      simp [c8ProdThreePerm_pow_three]

lemma c8Fin4Cycle_pow_twelve :
    (c8Fin4Cycle ^ 12) = 1 := by
  calc
    c8Fin4Cycle ^ 12 = (c8Fin4Cycle ^ 4) ^ 3 := by
      have h12 : (12 : ℕ) = 4 * 3 := by decide
      simpa [h12] using (pow_mul c8Fin4Cycle 4 3)
    _ = 1 := by
      simp [c8Fin4Cycle_pow_four]

lemma c8Fin5Cycle_pow_fifteen :
    (c8Fin5Cycle ^ 15) = 1 := by
  calc
    c8Fin5Cycle ^ 15 = (c8Fin5Cycle ^ 5) ^ 3 := by
      have h15 : (15 : ℕ) = 5 * 3 := by decide
      simpa [h15] using (pow_mul c8Fin5Cycle 5 3)
    _ = 1 := by
      simp [c8Fin5Cycle_pow_five]

lemma c8PowFour_transport
    {A B : Type*} (e : A ≃ B) (φ : Equiv.Perm B)
    (hPow : φ ^ 4 = 1) :
    ((e.trans φ).trans e.symm) ^ 4 = 1 := by
  apply Equiv.Perm.ext
  intro a
  apply e.injective
  have hConjPowAt : e ((((e.trans φ).trans e.symm) ^ 4) a) = (φ ^ 4) (e a) := by
    simp [pow_succ']
  have hPowAt : (φ ^ 4) (e a) = e a := by
    simpa using congrArg (fun q : Equiv.Perm B => q (e a)) hPow
  exact hConjPowAt.trans hPowAt

lemma c8PowFive_transport
    {A B : Type*} (e : A ≃ B) (φ : Equiv.Perm B)
    (hPow : φ ^ 5 = 1) :
    ((e.trans φ).trans e.symm) ^ 5 = 1 := by
  apply Equiv.Perm.ext
  intro a
  apply e.injective
  have hConjPowAt : e ((((e.trans φ).trans e.symm) ^ 5) a) = (φ ^ 5) (e a) := by
    simp [pow_succ']
  have hPowAt : (φ ^ 5) (e a) = e a := by
    simpa using congrArg (fun q : Equiv.Perm B => q (e a)) hPow
  exact hConjPowAt.trans hPowAt

lemma c8PowTwelve_transport
    {A B : Type*} (e : A ≃ B) (φ : Equiv.Perm B)
    (hPow : φ ^ 12 = 1) :
    ((e.trans φ).trans e.symm) ^ 12 = 1 := by
  apply Equiv.Perm.ext
  intro a
  apply e.injective
  have hConjPowAt : e ((((e.trans φ).trans e.symm) ^ 12) a) = (φ ^ 12) (e a) := by
    simp [pow_succ']
  have hPowAt : (φ ^ 12) (e a) = e a := by
    simpa using congrArg (fun q : Equiv.Perm B => q (e a)) hPow
  exact hConjPowAt.trans hPowAt

lemma c8PowFifteen_transport
    {A B : Type*} (e : A ≃ B) (φ : Equiv.Perm B)
    (hPow : φ ^ 15 = 1) :
    ((e.trans φ).trans e.symm) ^ 15 = 1 := by
  apply Equiv.Perm.ext
  intro a
  apply e.injective
  have hConjPowAt : e ((((e.trans φ).trans e.symm) ^ 15) a) = (φ ^ 15) (e a) := by
    simp [pow_succ']
  have hPowAt : (φ ^ 15) (e a) = e a := by
    simpa using congrArg (fun q : Equiv.Perm B => q (e a)) hPow
  exact hConjPowAt.trans hPowAt

lemma c8Conj_pow_apply
    {A B : Type*} (e : A ≃ B) (ψ : Equiv.Perm B) :
    ∀ k : ℕ, ∀ a : A,
      e ((((e.trans ψ).trans e.symm) ^ k) a) = (ψ ^ k) (e a) := by
  intro k
  induction k with
  | zero =>
      intro a
      simp
  | succ k ih =>
      intro a
      calc
        e ((((e.trans ψ).trans e.symm) ^ (k + 1)) a)
            = e (((e.trans ψ).trans e.symm) ((((e.trans ψ).trans e.symm) ^ k) a)) := by
                simp [pow_succ']
        _ = ψ (e ((((e.trans ψ).trans e.symm) ^ k) a)) := by simp
        _ = ψ ((ψ ^ k) (e a)) := by simp [ih]
        _ = (ψ ^ (k + 1)) (e a) := by simp [pow_succ']

lemma c8ThreeOrbit_of_sumCongr_inl
    {A α β : Type*}
    (e : A ≃ α ⊕ β)
    (τ : Equiv.Perm α)
    (σ : Equiv.Perm β)
    (hτ3 : τ ^ 3 = 1)
    {t : A} {a : α} (ha : e t = Sum.inl a) :
    (((e.trans (Equiv.Perm.sumCongr τ σ)).trans e.symm) ^ 3) t = t := by
  apply e.injective
  have hpow3 :
      ((Equiv.Perm.sumCongr τ σ) ^ 3) =
        Equiv.Perm.sumCongr (τ ^ 3) (σ ^ 3) := by
    simpa using
      (MonoidHom.map_pow
        (Equiv.Perm.sumCongrHom α β)
        (τ, σ) 3).symm
  calc
    e ((((e.trans (Equiv.Perm.sumCongr τ σ)).trans e.symm) ^ 3) t)
        = ((Equiv.Perm.sumCongr τ σ) ^ 3) (e t) := by
            simpa using c8Conj_pow_apply e (Equiv.Perm.sumCongr τ σ) 3 t
    _ = ((Equiv.Perm.sumCongr τ σ) ^ 3) (Sum.inl a) := by simp [ha]
    _ = (Equiv.Perm.sumCongr (τ ^ 3) (σ ^ 3)) (Sum.inl a) := by simp [hpow3]
    _ = Sum.inl ((τ ^ 3) a) := by simp
    _ = Sum.inl a := by simp [hτ3]
    _ = e t := by simp [ha]

lemma c8BigOrbit_of_sumCongr_inr_fin4
    {A α : Type*}
    (e : A ≃ α ⊕ C8Fin4)
    (τ : Equiv.Perm α)
    {t : A} {b : C8Fin4} (hb : e t = Sum.inr b) :
    t ∈ orbitSet
      ((e.trans (Equiv.Perm.sumCongr τ c8Fin4Cycle)).trans e.symm)
      (e.symm (Sum.inr 0)) := by
  refine ⟨b.1, ?_⟩
  apply e.injective
  have hpow :
      ((Equiv.Perm.sumCongr τ c8Fin4Cycle) ^ b.1) =
        Equiv.Perm.sumCongr (τ ^ b.1) (c8Fin4Cycle ^ b.1) := by
    simpa using
      (MonoidHom.map_pow
        (Equiv.Perm.sumCongrHom α C8Fin4)
        (τ, c8Fin4Cycle) b.1).symm
  calc
    e ((((e.trans (Equiv.Perm.sumCongr τ c8Fin4Cycle)).trans e.symm) ^ b.1)
        (e.symm (Sum.inr 0)))
        = ((Equiv.Perm.sumCongr τ c8Fin4Cycle) ^ b.1) (e (e.symm (Sum.inr 0))) := by
            simpa using
              c8Conj_pow_apply e (Equiv.Perm.sumCongr τ c8Fin4Cycle) b.1 (e.symm (Sum.inr 0))
    _ = ((Equiv.Perm.sumCongr τ c8Fin4Cycle) ^ b.1) (Sum.inr 0) := by simp
    _ = (Equiv.Perm.sumCongr (τ ^ b.1) (c8Fin4Cycle ^ b.1)) (Sum.inr 0) := by
          simp [hpow]
    _ = Sum.inr ((c8Fin4Cycle ^ b.1) 0) := by simp
    _ = Sum.inr b := by
          have hbpow : (c8Fin4Cycle ^ b.1) 0 = b := by
            fin_cases b <;> decide
          simp [hbpow]
    _ = e t := by simp [hb]

lemma c8BigOrbit_of_sumCongr_inr_fin5
    {A α : Type*}
    (e : A ≃ α ⊕ C8Fin5)
    (τ : Equiv.Perm α)
    {t : A} {b : C8Fin5} (hb : e t = Sum.inr b) :
    t ∈ orbitSet
      ((e.trans (Equiv.Perm.sumCongr τ c8Fin5Cycle)).trans e.symm)
      (e.symm (Sum.inr 0)) := by
  refine ⟨b.1, ?_⟩
  apply e.injective
  have hpow :
      ((Equiv.Perm.sumCongr τ c8Fin5Cycle) ^ b.1) =
        Equiv.Perm.sumCongr (τ ^ b.1) (c8Fin5Cycle ^ b.1) := by
    simpa using
      (MonoidHom.map_pow
        (Equiv.Perm.sumCongrHom α C8Fin5)
        (τ, c8Fin5Cycle) b.1).symm
  calc
    e ((((e.trans (Equiv.Perm.sumCongr τ c8Fin5Cycle)).trans e.symm) ^ b.1)
        (e.symm (Sum.inr 0)))
        = ((Equiv.Perm.sumCongr τ c8Fin5Cycle) ^ b.1) (e (e.symm (Sum.inr 0))) := by
            simpa using
              c8Conj_pow_apply e (Equiv.Perm.sumCongr τ c8Fin5Cycle) b.1 (e.symm (Sum.inr 0))
    _ = ((Equiv.Perm.sumCongr τ c8Fin5Cycle) ^ b.1) (Sum.inr 0) := by simp
    _ = (Equiv.Perm.sumCongr (τ ^ b.1) (c8Fin5Cycle ^ b.1)) (Sum.inr 0) := by
          simp [hpow]
    _ = Sum.inr ((c8Fin5Cycle ^ b.1) 0) := by simp
    _ = Sum.inr b := by
          have hbpow : (c8Fin5Cycle ^ b.1) 0 = b := by
            fin_cases b <;> decide
          simp [hbpow]
    _ = e t := by simp [hb]

/-- Paper-faithful Case-1 orbit-partition data:
`φ` has one 4-cycle (the designated big block) and all remaining orbits are
3-cycles; hence `period = 4` when no 3-block tail exists and `period = 12`
otherwise. -/
structure C8Case1OrbitPartitionData (X : Type uX) where
  φ : Equiv.Perm X
  period : ℕ
  hPeriod : period = 4 ∨ period = 12
  hPow : φ ^ period = 1
  hNoFix : ∀ t : X, φ t ≠ t
  x : X
  y : X
  z : X
  w : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hzw : z ≠ w
  hwx : w ≠ x
  hφx : φ x = y
  hφy : φ y = z
  hφz : φ z = w
  hφw : φ w = x
  hClassify : ∀ t : X, (φ ^ 3) t = t ∨ t ∈ orbitSet φ x

/-- Paper-faithful Case-2 orbit-partition data:
`φ` has one 5-cycle (the designated big block) and all remaining orbits are
3-cycles; hence `period = 5` when no 3-block tail exists and `period = 15`
otherwise. -/
structure C8Case2OrbitPartitionData (X : Type uX) where
  φ : Equiv.Perm X
  period : ℕ
  hPeriod : period = 5 ∨ period = 15
  hPow : φ ^ period = 1
  hNoFix : ∀ t : X, φ t ≠ t
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
  hφx : φ x = y
  hφy : φ y = z
  hφz : φ z = u
  hφu : φ u = v
  hφv : φ v = x
  hClassify : ∀ t : X, (φ ^ 3) t = t ∨ t ∈ orbitSet φ x

theorem c8Card_eq_mul_three_add_four_of_case1
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    ∃ q : ℕ, Fintype.card X = q * 3 + 4 := by
  have hmod : Nat.ModEq 3 1 (Fintype.card X) := by
    change 1 % 3 = Fintype.card X % 3
    simp [hCase1]
  have hPos : 0 < Fintype.card X := lt_trans (by decide : 0 < 2) hCardGtTwo
  have hOneLe : 1 ≤ Fintype.card X := Nat.succ_le_of_lt hPos
  rcases (Nat.modEq_iff_exists_eq_add hOneLe).1 hmod with ⟨t, ht⟩
  cases t with
  | zero =>
      exfalso
      have hCardOne : Fintype.card X = 1 := by simpa using ht
      omega
  | succ q =>
      refine ⟨q, ?_⟩
      omega

theorem c8Card_eq_mul_three_add_five_of_case2
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    ∃ q : ℕ, Fintype.card X = q * 3 + 5 := by
  have hmod : Nat.ModEq 3 2 (Fintype.card X) := by
    change 2 % 3 = Fintype.card X % 3
    simp [hCase2]
  have hTwoLe : 2 ≤ Fintype.card X := Nat.le_of_lt hCardGtTwo
  rcases (Nat.modEq_iff_exists_eq_add hTwoLe).1 hmod with ⟨t, ht⟩
  cases t with
  | zero =>
      exfalso
      have hCardTwo : Fintype.card X = 2 := by simpa using ht
      omega
  | succ q =>
      refine ⟨q, ?_⟩
      omega

noncomputable def c8Case1OrbitPartitionData_of_card_eq_mul_three_add_four
    [Fintype X]
    (q : ℕ) (hCard : Fintype.card X = q * 3 + 4) :
    C8Case1OrbitPartitionData X := by
  let eFin : X ≃ Fin (q * 3 + 4) := Fintype.equivFinOfCardEq hCard
  let eSplit : X ≃ Fin (q * 3) ⊕ C8Fin4 := eFin.trans finSumFinEquiv.symm
  let eAll : X ≃ (Fin q × C8Fin3) ⊕ C8Fin4 :=
    eSplit.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl C8Fin4))
  let ψ : Equiv.Perm ((Fin q × C8Fin3) ⊕ C8Fin4) :=
    Equiv.Perm.sumCongr (c8ProdThreePerm q) c8Fin4Cycle
  have hψNoFix : ∀ s : (Fin q × C8Fin3) ⊕ C8Fin4, ψ s ≠ s := by
    intro s
    cases s with
    | inl a =>
        simpa [ψ] using c8ProdThreePerm_no_fixed q a
    | inr b =>
        simpa [ψ] using c8Fin4Cycle_no_fixed b
  have hψPow12 : ψ ^ 12 = 1 := by
    calc
      ψ ^ 12 =
          Equiv.Perm.sumCongr ((c8ProdThreePerm q) ^ 12) (c8Fin4Cycle ^ 12) := by
            simpa [ψ] using
              (MonoidHom.map_pow
                (Equiv.Perm.sumCongrHom (Fin q × C8Fin3) C8Fin4)
                (c8ProdThreePerm q, c8Fin4Cycle) 12).symm
      _ = Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin q × C8Fin3)) (1 : Equiv.Perm C8Fin4) := by
            simp [c8ProdThreePerm_pow_twelve, c8Fin4Cycle_pow_twelve]
      _ = 1 := by simp
  have hψPow4_of_qzero (hq : q = 0) : ψ ^ 4 = 1 := by
    subst hq
    have hTailPow4 : (c8ProdThreePerm 0) ^ 4 = 1 := by
      apply Equiv.Perm.ext
      intro p
      rcases p with ⟨a, b⟩
      exact False.elim (Fin.elim0 a)
    calc
      ψ ^ 4 =
          Equiv.Perm.sumCongr ((c8ProdThreePerm 0) ^ 4) (c8Fin4Cycle ^ 4) := by
            simpa [ψ] using
              (MonoidHom.map_pow
                (Equiv.Perm.sumCongrHom (Fin 0 × C8Fin3) C8Fin4)
                (c8ProdThreePerm 0, c8Fin4Cycle) 4).symm
      _ = Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 0 × C8Fin3)) (1 : Equiv.Perm C8Fin4) := by
            simp [hTailPow4, c8Fin4Cycle_pow_four]
      _ = 1 := by simp
  by_cases hq : q = 0
  · subst hq
    refine
      { φ := (eAll.trans ψ).trans eAll.symm
        period := 4
        hPeriod := Or.inl rfl
        hPow := c8PowFour_transport eAll ψ (hψPow4_of_qzero rfl)
        hNoFix := c8NoFixed_transport eAll ψ hψNoFix
        x := eAll.symm (Sum.inr 0)
        y := eAll.symm (Sum.inr 1)
        z := eAll.symm (Sum.inr 2)
        w := eAll.symm (Sum.inr 3)
        hxy := ?_
        hyz := ?_
        hzx := ?_
        hzw := ?_
        hwx := ?_
        hφx := ?_
        hφy := ?_
        hφz := ?_
        hφw := ?_
        hClassify := ?_ }
    · intro h
      have hs : (Sum.inr (0 : C8Fin4) : (Fin 0 × C8Fin3) ⊕ C8Fin4) = Sum.inr (1 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (1 : C8Fin4) : (Fin 0 × C8Fin3) ⊕ C8Fin4) = Sum.inr (2 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin4) : (Fin 0 × C8Fin3) ⊕ C8Fin4) = Sum.inr (0 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin4) : (Fin 0 × C8Fin3) ⊕ C8Fin4) = Sum.inr (3 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (3 : C8Fin4) : (Fin 0 × C8Fin3) ⊕ C8Fin4) = Sum.inr (0 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply0]
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply1]
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply2]
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply3]
    · intro t
      rcases h : eAll t with ⟨a, b⟩ | b
      · exact False.elim (Fin.elim0 a)
      · right
        simpa [ψ] using
          (c8BigOrbit_of_sumCongr_inr_fin4
            (e := eAll) (τ := c8ProdThreePerm 0) (hb := h))
  · refine
      { φ := (eAll.trans ψ).trans eAll.symm
        period := 12
        hPeriod := Or.inr rfl
        hPow := c8PowTwelve_transport eAll ψ hψPow12
        hNoFix := c8NoFixed_transport eAll ψ hψNoFix
        x := eAll.symm (Sum.inr 0)
        y := eAll.symm (Sum.inr 1)
        z := eAll.symm (Sum.inr 2)
        w := eAll.symm (Sum.inr 3)
        hxy := ?_
        hyz := ?_
        hzx := ?_
        hzw := ?_
        hwx := ?_
        hφx := ?_
        hφy := ?_
        hφz := ?_
        hφw := ?_
        hClassify := ?_ }
    · intro h
      have hs : (Sum.inr (0 : C8Fin4) : (Fin q × C8Fin3) ⊕ C8Fin4) = Sum.inr (1 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (1 : C8Fin4) : (Fin q × C8Fin3) ⊕ C8Fin4) = Sum.inr (2 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin4) : (Fin q × C8Fin3) ⊕ C8Fin4) = Sum.inr (0 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin4) : (Fin q × C8Fin3) ⊕ C8Fin4) = Sum.inr (3 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (3 : C8Fin4) : (Fin q × C8Fin3) ⊕ C8Fin4) = Sum.inr (0 : C8Fin4) := by
        simpa using congrArg eAll h
      cases hs
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply0]
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply1]
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply2]
    · apply eAll.injective
      simp [ψ, c8Fin4Cycle_apply3]
    · intro t
      rcases h : eAll t with a | b
      · left
        simpa [ψ] using
          (c8ThreeOrbit_of_sumCongr_inl
            (e := eAll) (τ := c8ProdThreePerm q) (σ := c8Fin4Cycle)
            (hτ3 := c8ProdThreePerm_pow_three q) (ha := h))
      · right
        simpa [ψ] using
          (c8BigOrbit_of_sumCongr_inr_fin4
            (e := eAll) (τ := c8ProdThreePerm q) (hb := h))

noncomputable def c8Case2OrbitPartitionData_of_card_eq_mul_three_add_five
    [Fintype X]
    (q : ℕ) (hCard : Fintype.card X = q * 3 + 5) :
    C8Case2OrbitPartitionData X := by
  let eFin : X ≃ Fin (q * 3 + 5) := Fintype.equivFinOfCardEq hCard
  let eSplit : X ≃ Fin (q * 3) ⊕ C8Fin5 := eFin.trans finSumFinEquiv.symm
  let eAll : X ≃ (Fin q × C8Fin3) ⊕ C8Fin5 :=
    eSplit.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl C8Fin5))
  let ψ : Equiv.Perm ((Fin q × C8Fin3) ⊕ C8Fin5) :=
    Equiv.Perm.sumCongr (c8ProdThreePerm q) c8Fin5Cycle
  have hψNoFix : ∀ s : (Fin q × C8Fin3) ⊕ C8Fin5, ψ s ≠ s := by
    intro s
    cases s with
    | inl a =>
        simpa [ψ] using c8ProdThreePerm_no_fixed q a
    | inr b =>
        simpa [ψ] using c8Fin5Cycle_no_fixed b
  have hψPow15 : ψ ^ 15 = 1 := by
    calc
      ψ ^ 15 =
          Equiv.Perm.sumCongr ((c8ProdThreePerm q) ^ 15) (c8Fin5Cycle ^ 15) := by
            simpa [ψ] using
              (MonoidHom.map_pow
                (Equiv.Perm.sumCongrHom (Fin q × C8Fin3) C8Fin5)
                (c8ProdThreePerm q, c8Fin5Cycle) 15).symm
      _ = Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin q × C8Fin3)) (1 : Equiv.Perm C8Fin5) := by
            simp [c8ProdThreePerm_pow_fifteen, c8Fin5Cycle_pow_fifteen]
      _ = 1 := by simp
  have hψPow5_of_qzero (hq : q = 0) : ψ ^ 5 = 1 := by
    subst hq
    have hTailPow5 : (c8ProdThreePerm 0) ^ 5 = 1 := by
      apply Equiv.Perm.ext
      intro p
      rcases p with ⟨a, b⟩
      exact False.elim (Fin.elim0 a)
    calc
      ψ ^ 5 =
          Equiv.Perm.sumCongr ((c8ProdThreePerm 0) ^ 5) (c8Fin5Cycle ^ 5) := by
            simpa [ψ] using
              (MonoidHom.map_pow
                (Equiv.Perm.sumCongrHom (Fin 0 × C8Fin3) C8Fin5)
                (c8ProdThreePerm 0, c8Fin5Cycle) 5).symm
      _ = Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 0 × C8Fin3)) (1 : Equiv.Perm C8Fin5) := by
            simp [hTailPow5, c8Fin5Cycle_pow_five]
      _ = 1 := by simp
  by_cases hq : q = 0
  · subst hq
    refine
      { φ := (eAll.trans ψ).trans eAll.symm
        period := 5
        hPeriod := Or.inl rfl
        hPow := c8PowFive_transport eAll ψ (hψPow5_of_qzero rfl)
        hNoFix := c8NoFixed_transport eAll ψ hψNoFix
        x := eAll.symm (Sum.inr 0)
        y := eAll.symm (Sum.inr 1)
        z := eAll.symm (Sum.inr 2)
        u := eAll.symm (Sum.inr 3)
        v := eAll.symm (Sum.inr 4)
        hxy := ?_
        hyz := ?_
        hzx := ?_
        hzu := ?_
        huv := ?_
        hvx := ?_
        hφx := ?_
        hφy := ?_
        hφz := ?_
        hφu := ?_
        hφv := ?_
        hClassify := ?_ }
    · intro h
      have hs : (Sum.inr (0 : C8Fin5) : (Fin 0 × C8Fin3) ⊕ C8Fin5) = Sum.inr (1 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (1 : C8Fin5) : (Fin 0 × C8Fin3) ⊕ C8Fin5) = Sum.inr (2 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin5) : (Fin 0 × C8Fin3) ⊕ C8Fin5) = Sum.inr (0 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin5) : (Fin 0 × C8Fin3) ⊕ C8Fin5) = Sum.inr (3 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (3 : C8Fin5) : (Fin 0 × C8Fin3) ⊕ C8Fin5) = Sum.inr (4 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (4 : C8Fin5) : (Fin 0 × C8Fin3) ⊕ C8Fin5) = Sum.inr (0 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply0]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply1]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply2]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply3]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply4]
    · intro t
      rcases h : eAll t with ⟨a, b⟩ | b
      · exact False.elim (Fin.elim0 a)
      · right
        simpa [ψ] using
          (c8BigOrbit_of_sumCongr_inr_fin5
            (e := eAll) (τ := c8ProdThreePerm 0) (hb := h))
  · refine
      { φ := (eAll.trans ψ).trans eAll.symm
        period := 15
        hPeriod := Or.inr rfl
        hPow := c8PowFifteen_transport eAll ψ hψPow15
        hNoFix := c8NoFixed_transport eAll ψ hψNoFix
        x := eAll.symm (Sum.inr 0)
        y := eAll.symm (Sum.inr 1)
        z := eAll.symm (Sum.inr 2)
        u := eAll.symm (Sum.inr 3)
        v := eAll.symm (Sum.inr 4)
        hxy := ?_
        hyz := ?_
        hzx := ?_
        hzu := ?_
        huv := ?_
        hvx := ?_
        hφx := ?_
        hφy := ?_
        hφz := ?_
        hφu := ?_
        hφv := ?_
        hClassify := ?_ }
    · intro h
      have hs : (Sum.inr (0 : C8Fin5) : (Fin q × C8Fin3) ⊕ C8Fin5) = Sum.inr (1 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (1 : C8Fin5) : (Fin q × C8Fin3) ⊕ C8Fin5) = Sum.inr (2 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin5) : (Fin q × C8Fin3) ⊕ C8Fin5) = Sum.inr (0 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (2 : C8Fin5) : (Fin q × C8Fin3) ⊕ C8Fin5) = Sum.inr (3 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (3 : C8Fin5) : (Fin q × C8Fin3) ⊕ C8Fin5) = Sum.inr (4 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · intro h
      have hs : (Sum.inr (4 : C8Fin5) : (Fin q × C8Fin3) ⊕ C8Fin5) = Sum.inr (0 : C8Fin5) := by
        simpa using congrArg eAll h
      cases hs
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply0]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply1]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply2]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply3]
    · apply eAll.injective
      simp [ψ, c8Fin5Cycle_apply4]
    · intro t
      rcases h : eAll t with a | b
      · left
        simpa [ψ] using
          (c8ThreeOrbit_of_sumCongr_inl
            (e := eAll) (τ := c8ProdThreePerm q) (σ := c8Fin5Cycle)
            (hτ3 := c8ProdThreePerm_pow_three q) (ha := h))
      · right
        simpa [ψ] using
          (c8BigOrbit_of_sumCongr_inr_fin5
            (e := eAll) (τ := c8ProdThreePerm q) (hb := h))

theorem c8Case1OrbitPartitionData_of_case1
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    Nonempty (C8Case1OrbitPartitionData X) := by
  rcases c8Card_eq_mul_three_add_four_of_case1 (X := X) hCardGtTwo hCase1 with ⟨q, hCard⟩
  exact ⟨c8Case1OrbitPartitionData_of_card_eq_mul_three_add_four (X := X) q hCard⟩

theorem c8Case2OrbitPartitionData_of_case2
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    Nonempty (C8Case2OrbitPartitionData X) := by
  rcases c8Card_eq_mul_three_add_five_of_case2 (X := X) hCardGtTwo hCase2 with ⟨q, hCard⟩
  exact ⟨c8Case2OrbitPartitionData_of_card_eq_mul_three_add_five (X := X) q hCard⟩

lemma C8Cycle3OrbitData.mem_orbitSet_z (c : C8Cycle3OrbitData X) :
    c.z ∈ orbitSet c.φ c.x := by
  refine ⟨1, ?_⟩
  simpa using c.hφx

lemma C8Cycle3OrbitData.mem_orbitSet_y (c : C8Cycle3OrbitData X) :
    c.y ∈ orbitSet c.φ c.x := by
  refine ⟨2, ?_⟩
  calc
    (c.φ ^ 2) c.x = c.φ (c.φ c.x) := by simp [pow_succ']
    _ = c.φ c.z := by simp [c.hφx]
    _ = c.y := c.hφz

end C8OrbitCases

end Pivato
