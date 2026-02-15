import Pivato.Theorem2.C8Branch
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# C.8 orbit/case infrastructure

This file isolates reusable combinatorial/permutation infrastructure for the
C.8 bridge:
- point-pattern extraction from `% 3` cardinal regimes;
- orbit-cycle data records (length 3/4/5);
- small transport lemmas into `orbitSet`.
-/

namespace Pivato

section C8OrbitCases

universe uX

variable {X : Type uX}

/-- Combinatorial point-pattern used for 4-cycle fallback packaging. -/
structure C8FallbackPointPattern4 (X : Type uX) where
  x : X
  y : X
  z : X
  w : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hzw : z ≠ w
  hwx : w ≠ x

/-- Combinatorial point-pattern used for 5-cycle fallback packaging. -/
structure C8FallbackPointPattern5 (X : Type uX) where
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

lemma c8Fallback_pointPattern4_of_case1
    [Fintype X] [DecidableEq X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    Nonempty (C8FallbackPointPattern4 X) := by
  have hge3 : 3 ≤ Fintype.card X := Nat.succ_le_of_lt hCardGtTwo
  have hne3 : Fintype.card X ≠ 3 := by
    intro h3
    have hCase1' := hCase1
    simp [h3] at hCase1'
  have h3ne : 3 ≠ Fintype.card X := by
    intro h
    exact hne3 h.symm
  have hgt3 : 3 < Fintype.card X := lt_of_le_of_ne hge3 h3ne
  have hUniv : 3 < (Finset.univ : Finset X).card := by
    simpa using hgt3
  rcases (Finset.three_lt_card).1 hUniv with
    ⟨x, _hx, y, _hy, z, _hz, w, _hw, hxy, hxz, hxw, hyz, _hyw, hzw⟩
  exact ⟨⟨x, y, z, w, hxy, hyz, hxz.symm, hzw, hxw.symm⟩⟩

lemma c8Fallback_pointPattern5_of_case2
    [Fintype X] [DecidableEq X] [Nonempty X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    Nonempty (C8FallbackPointPattern5 X) := by
  classical
  have hge3 : 3 ≤ Fintype.card X := Nat.succ_le_of_lt hCardGtTwo
  have hne3 : Fintype.card X ≠ 3 := by
    intro h3
    have hCase2' := hCase2
    simp [h3] at hCase2'
  have h3ne : 3 ≠ Fintype.card X := by
    intro h
    exact hne3 h.symm
  have hgt3 : 3 < Fintype.card X := lt_of_le_of_ne hge3 h3ne
  have hge4 : 4 ≤ Fintype.card X := Nat.succ_le_of_lt hgt3
  have hne4 : Fintype.card X ≠ 4 := by
    intro h4
    have hCase2' := hCase2
    simp [h4] at hCase2'
  have h4ne : 4 ≠ Fintype.card X := by
    intro h
    exact hne4 h.symm
  have hgt4 : 4 < Fintype.card X := lt_of_le_of_ne hge4 h4ne
  obtain ⟨x⟩ := ‹Nonempty X›
  let s : Finset X := (Finset.univ : Finset X).erase x
  have hsSucc : s.card + 1 = Fintype.card X := by
    dsimp [s]
    simpa using
      (Finset.card_erase_add_one (s := (Finset.univ : Finset X)) (a := x) (by simp))
  have hsGtThree : 3 < s.card := by
    have h4 : 4 < s.card + 1 := by
      simpa [hsSucc] using hgt4
    have h4' : Nat.succ 3 < Nat.succ s.card := by
      simpa [Nat.succ_eq_add_one] using h4
    exact Nat.lt_of_succ_lt_succ h4'
  rcases (Finset.three_lt_card).1 hsGtThree with
    ⟨y, hy, z, hz, u, _hu, v, hv, hyz, _hyu, _hyv, hzu, _hzv, huv⟩
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
  have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
  exact ⟨⟨x, y, z, u, v, hyx.symm, hyz, hzx, hzu, huv, hvx⟩⟩

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

/-- Orbit-data package for the 4-cycle fallback branch. -/
structure C8Cycle4OrbitData (X : Type uX) where
  φ : Equiv.Perm X
  hPow : φ ^ 4 = 1
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

/-- Orbit-data package for the 5-cycle fallback branch. -/
structure C8Cycle5OrbitData (X : Type uX) where
  φ : Equiv.Perm X
  hPow : φ ^ 5 = 1
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

noncomputable def c8Cycle4OrbitData_of_card_eq_add_four
    [Fintype X]
    (m : ℕ) (hCard : Fintype.card X = m + 4) :
    C8Cycle4OrbitData X := by
  let eFin : X ≃ Fin (m + 4) := Fintype.equivFinOfCardEq hCard
  let eSplit : X ≃ Fin m ⊕ C8Fin4 := eFin.trans finSumFinEquiv.symm
  let ψ : Equiv.Perm (Fin m ⊕ C8Fin4) :=
    Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin m)) c8Fin4Cycle
  have hψPow : ψ ^ 4 = 1 := by
    apply Equiv.Perm.ext
    intro s
    cases s with
    | inl a =>
        simp [ψ, pow_succ']
    | inr b =>
        have hb : (c8Fin4Cycle ^ 4) b = b := by
          simpa using congrArg (fun q : Equiv.Perm C8Fin4 => q b) c8Fin4Cycle_pow_four
        simpa [ψ, pow_succ'] using hb
  refine
    { φ := (eSplit.trans ψ).trans eSplit.symm
      hPow := c8PowFour_transport eSplit ψ hψPow
      x := eSplit.symm (Sum.inr 0)
      y := eSplit.symm (Sum.inr 1)
      z := eSplit.symm (Sum.inr 2)
      w := eSplit.symm (Sum.inr 3)
      hxy := ?_
      hyz := ?_
      hzx := ?_
      hzw := ?_
      hwx := ?_
      hφx := ?_
      hφy := ?_
      hφz := ?_
      hφw := ?_ }
  · intro h
    have hs : (Sum.inr (0 : C8Fin4) : Fin m ⊕ C8Fin4) = Sum.inr (1 : C8Fin4) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (1 : C8Fin4) : Fin m ⊕ C8Fin4) = Sum.inr (2 : C8Fin4) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (2 : C8Fin4) : Fin m ⊕ C8Fin4) = Sum.inr (0 : C8Fin4) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (2 : C8Fin4) : Fin m ⊕ C8Fin4) = Sum.inr (3 : C8Fin4) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (3 : C8Fin4) : Fin m ⊕ C8Fin4) = Sum.inr (0 : C8Fin4) := by
      simpa using congrArg eSplit h
    cases hs
  · apply eSplit.injective
    simp [ψ, c8Fin4Cycle_apply0]
  · apply eSplit.injective
    simp [ψ, c8Fin4Cycle_apply1]
  · apply eSplit.injective
    simp [ψ, c8Fin4Cycle_apply2]
  · apply eSplit.injective
    simp [ψ, c8Fin4Cycle_apply3]

noncomputable def c8Cycle5OrbitData_of_card_eq_add_five
    [Fintype X]
    (m : ℕ) (hCard : Fintype.card X = m + 5) :
    C8Cycle5OrbitData X := by
  let eFin : X ≃ Fin (m + 5) := Fintype.equivFinOfCardEq hCard
  let eSplit : X ≃ Fin m ⊕ C8Fin5 := eFin.trans finSumFinEquiv.symm
  let ψ : Equiv.Perm (Fin m ⊕ C8Fin5) :=
    Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin m)) c8Fin5Cycle
  have hψPow : ψ ^ 5 = 1 := by
    apply Equiv.Perm.ext
    intro s
    cases s with
    | inl a =>
        simp [ψ, pow_succ']
    | inr b =>
        have hb : (c8Fin5Cycle ^ 5) b = b := by
          simpa using congrArg (fun q : Equiv.Perm C8Fin5 => q b) c8Fin5Cycle_pow_five
        simpa [ψ, pow_succ'] using hb
  refine
    { φ := (eSplit.trans ψ).trans eSplit.symm
      hPow := c8PowFive_transport eSplit ψ hψPow
      x := eSplit.symm (Sum.inr 0)
      y := eSplit.symm (Sum.inr 1)
      z := eSplit.symm (Sum.inr 2)
      u := eSplit.symm (Sum.inr 3)
      v := eSplit.symm (Sum.inr 4)
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
      hφv := ?_ }
  · intro h
    have hs : (Sum.inr (0 : C8Fin5) : Fin m ⊕ C8Fin5) = Sum.inr (1 : C8Fin5) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (1 : C8Fin5) : Fin m ⊕ C8Fin5) = Sum.inr (2 : C8Fin5) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (2 : C8Fin5) : Fin m ⊕ C8Fin5) = Sum.inr (0 : C8Fin5) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (2 : C8Fin5) : Fin m ⊕ C8Fin5) = Sum.inr (3 : C8Fin5) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (3 : C8Fin5) : Fin m ⊕ C8Fin5) = Sum.inr (4 : C8Fin5) := by
      simpa using congrArg eSplit h
    cases hs
  · intro h
    have hs : (Sum.inr (4 : C8Fin5) : Fin m ⊕ C8Fin5) = Sum.inr (0 : C8Fin5) := by
      simpa using congrArg eSplit h
    cases hs
  · apply eSplit.injective
    simp [ψ, c8Fin5Cycle_apply0]
  · apply eSplit.injective
    simp [ψ, c8Fin5Cycle_apply1]
  · apply eSplit.injective
    simp [ψ, c8Fin5Cycle_apply2]
  · apply eSplit.injective
    simp [ψ, c8Fin5Cycle_apply3]
  · apply eSplit.injective
    simp [ψ, c8Fin5Cycle_apply4]

theorem c8Cycle4OrbitData_of_case1
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    Nonempty (C8Cycle4OrbitData X) := by
  have hge3 : 3 ≤ Fintype.card X := Nat.succ_le_of_lt hCardGtTwo
  have hne3 : Fintype.card X ≠ 3 := by
    intro h3
    have hCase1' := hCase1
    simp [h3] at hCase1'
  have h3ne : 3 ≠ Fintype.card X := by
    intro h
    exact hne3 h.symm
  have hgt3 : 3 < Fintype.card X := lt_of_le_of_ne hge3 h3ne
  have hge4 : 4 ≤ Fintype.card X := Nat.succ_le_of_lt hgt3
  rcases Nat.exists_eq_add_of_le hge4 with ⟨m, hm⟩
  let hCard : Fintype.card X = m + 4 := by
    simpa [Nat.add_comm] using hm
  exact ⟨c8Cycle4OrbitData_of_card_eq_add_four (X := X) m hCard⟩

theorem c8Cycle5OrbitData_of_case2
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    Nonempty (C8Cycle5OrbitData X) := by
  have hge3 : 3 ≤ Fintype.card X := Nat.succ_le_of_lt hCardGtTwo
  have hne3 : Fintype.card X ≠ 3 := by
    intro h3
    have hCase2' := hCase2
    simp [h3] at hCase2'
  have h3ne : 3 ≠ Fintype.card X := by
    intro h
    exact hne3 h.symm
  have hgt3 : 3 < Fintype.card X := lt_of_le_of_ne hge3 h3ne
  have hge4 : 4 ≤ Fintype.card X := Nat.succ_le_of_lt hgt3
  have hne4 : Fintype.card X ≠ 4 := by
    intro h4
    have hCase2' := hCase2
    simp [h4] at hCase2'
  have h4ne : 4 ≠ Fintype.card X := by
    intro h
    exact hne4 h.symm
  have hgt4 : 4 < Fintype.card X := lt_of_le_of_ne hge4 h4ne
  have hge5 : 5 ≤ Fintype.card X := Nat.succ_le_of_lt hgt4
  rcases Nat.exists_eq_add_of_le hge5 with ⟨m, hm⟩
  let hCard : Fintype.card X = m + 5 := by
    simpa [Nat.add_comm] using hm
  exact ⟨c8Cycle5OrbitData_of_card_eq_add_five (X := X) m hCard⟩

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

lemma C8Cycle4OrbitData.mem_orbitSet_y (c : C8Cycle4OrbitData X) :
    c.y ∈ orbitSet c.φ c.x := by
  refine ⟨1, ?_⟩
  simpa using c.hφx

lemma C8Cycle4OrbitData.mem_orbitSet_z (c : C8Cycle4OrbitData X) :
    c.z ∈ orbitSet c.φ c.x := by
  refine ⟨2, ?_⟩
  calc
    (c.φ ^ 2) c.x = c.φ (c.φ c.x) := by simp [pow_succ']
    _ = c.φ c.y := by simp [c.hφx]
    _ = c.z := c.hφy

lemma C8Cycle4OrbitData.mem_orbitSet_w (c : C8Cycle4OrbitData X) :
    c.w ∈ orbitSet c.φ c.x := by
  refine ⟨3, ?_⟩
  calc
    (c.φ ^ 3) c.x = c.φ ((c.φ ^ 2) c.x) := by simp [pow_succ']
    _ = c.φ c.z := by
      simp [pow_succ', c.hφx, c.hφy]
    _ = c.w := c.hφz

lemma C8Cycle5OrbitData.mem_orbitSet_y (c : C8Cycle5OrbitData X) :
    c.y ∈ orbitSet c.φ c.x := by
  refine ⟨1, ?_⟩
  simpa using c.hφx

lemma C8Cycle5OrbitData.mem_orbitSet_z (c : C8Cycle5OrbitData X) :
    c.z ∈ orbitSet c.φ c.x := by
  refine ⟨2, ?_⟩
  calc
    (c.φ ^ 2) c.x = c.φ (c.φ c.x) := by simp [pow_succ']
    _ = c.φ c.y := by simp [c.hφx]
    _ = c.z := c.hφy

lemma C8Cycle5OrbitData.mem_orbitSet_u (c : C8Cycle5OrbitData X) :
    c.u ∈ orbitSet c.φ c.x := by
  refine ⟨3, ?_⟩
  calc
    (c.φ ^ 3) c.x = c.φ ((c.φ ^ 2) c.x) := by simp [pow_succ']
    _ = c.φ c.z := by
      simp [pow_succ', c.hφx, c.hφy]
    _ = c.u := c.hφz

lemma C8Cycle5OrbitData.mem_orbitSet_v (c : C8Cycle5OrbitData X) :
    c.v ∈ orbitSet c.φ c.x := by
  refine ⟨4, ?_⟩
  calc
    (c.φ ^ 4) c.x = c.φ ((c.φ ^ 3) c.x) := by simp [pow_succ']
    _ = c.φ c.u := by
      simp [pow_succ', c.hφx, c.hφy, c.hφz]
    _ = c.v := c.hφu

/-- Unified fallback orbit-case data: either a 4-cycle or a 5-cycle witness. -/
inductive C8FallbackOrbitCase (X : Type uX) where
  | four : C8Cycle4OrbitData X → C8FallbackOrbitCase X
  | five : C8Cycle5OrbitData X → C8FallbackOrbitCase X

namespace C8FallbackOrbitCase

def perm (c : C8FallbackOrbitCase X) : Equiv.Perm X :=
  match c with
  | .four d => d.φ
  | .five d => d.φ

def period (c : C8FallbackOrbitCase X) : ℕ :=
  match c with
  | .four _ => 4
  | .five _ => 5

lemma pow_period_eq_one (c : C8FallbackOrbitCase X) :
    c.perm ^ c.period = 1 := by
  cases c with
  | four d =>
      simpa [perm, period] using d.hPow
  | five d =>
      simpa [perm, period] using d.hPow

end C8FallbackOrbitCase

theorem c8FallbackOrbitCase_of_case1
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    Nonempty (C8FallbackOrbitCase X) := by
  rcases c8Cycle4OrbitData_of_case1 (X := X) hCardGtTwo hCase1 with ⟨d4⟩
  exact ⟨C8FallbackOrbitCase.four d4⟩

theorem c8FallbackOrbitCase_of_case2
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    Nonempty (C8FallbackOrbitCase X) := by
  rcases c8Cycle5OrbitData_of_case2 (X := X) hCardGtTwo hCase2 with ⟨d5⟩
  exact ⟨C8FallbackOrbitCase.five d5⟩

theorem c8FallbackOrbitCase_of_cases12
    [Fintype X]
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase12 : Fintype.card X % 3 = 1 ∨ Fintype.card X % 3 = 2) :
    Nonempty (C8FallbackOrbitCase X) := by
  rcases hCase12 with hCase1 | hCase2
  · exact c8FallbackOrbitCase_of_case1 (X := X) hCardGtTwo hCase1
  · exact c8FallbackOrbitCase_of_case2 (X := X) hCardGtTwo hCase2

end C8OrbitCases

end Pivato
