import Pivato.Theorem2.C8Branch
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
    ⟨x, hx, y, hy, z, hz, w, hw, hxy, hxz, hxw, hyz, hyw, hzw⟩
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
    ⟨y, hy, z, hz, u, hu, v, hv, hyz, hyu, hyv, hzu, hzv, huv⟩
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
  have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
  exact ⟨⟨x, y, z, u, v, hyx.symm, hyz, hzx, hzu, huv, hvx⟩⟩

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
  have _hPattern4 : Nonempty (C8FallbackPointPattern4 X) :=
    c8Fallback_pointPattern4_of_case1 (X := X) hCardGtTwo hCase1
  -- TODO: construct C.8.4 equation package(s) in the `% 3 = 1` regime.
  sorry

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
  have _hPattern5 : Nonempty (C8FallbackPointPattern5 X) :=
    c8Fallback_pointPattern5_of_case2 (X := X) hCardGtTwo hCase2
  -- TODO: construct C.8.4 equation package(s) in the `% 3 = 2` regime.
  sorry

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
