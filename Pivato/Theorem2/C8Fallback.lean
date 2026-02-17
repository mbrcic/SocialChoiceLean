import Pivato.Theorem2.C8OrbitCases

/-!
# Lemma C.8.4 fallback development

This module formalizes the Case 1/2 branch of Appendix C.8:
- paper-form equation packages `(C.9)--(C.14)` and `(C.15)--(C.20)`;
- designated reductions to Eq. (C.21);
- branch-split assembly (`C.8.3` vs `C.8.4`) via orbit-partition witnesses.
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
      balanceAt B x y d + balanceAt B y w d +
        balanceAt B w z d + balanceAt B z x d = 0
  eqC11 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d +
        balanceAt B x w d + balanceAt B w y d = 0
  eqC12 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z w d +
        balanceAt B w x d + balanceAt B x y d = 0
  eqC13 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x y d +
        balanceAt B y w d + balanceAt B w z d = 0
  eqC14 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x w d +
        balanceAt B w y d + balanceAt B y z d = 0

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
      balanceAt B x y d + balanceAt B y z d + balanceAt B z v d +
        balanceAt B v u d + balanceAt B u x d = 0
  eqC17 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d + balanceAt B x u d +
        balanceAt B u v d + balanceAt B v y d = 0
  eqC18 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d + balanceAt B x v d +
        balanceAt B v u d + balanceAt B u y d = 0
  eqC19 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x y d + balanceAt B y u d +
        balanceAt B u v d + balanceAt B v z d = 0
  eqC20 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x y d + balanceAt B y v d +
        balanceAt B v u d + balanceAt B u z d = 0

/-- C.8.4 fallback equation package: either the 4-cycle or 5-cycle package. -/
def C8FallbackEquationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) ∨
    Nonempty (C8FallbackEquationPack5 (D := D) (B := B))

/-- Paper-faithful Case-1 reduction:
from (C.9)--(C.14), derive Eq. (C.21) on the designated triple `(x,y,z)`. -/
theorem c8EqC21_designated_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (_hSkew : BalanceSkew (B := B))
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
        balanceAt B hPack4.z hPack4.x d = 0 := by
  /- TODO (paper C.8.4, Case 1):
     sum (C.9)--(C.14), cancel skew-symmetric opposite terms, obtain
     `4 • (b_xy + b_yz + b_zx) = 0`, then conclude the cycle-sum law. -/
  sorry

/-- Paper-faithful Case-2 reduction:
from (C.15)--(C.20), derive Eq. (C.21) on the designated triple `(x,y,z)`. -/
theorem c8EqC21_designated_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (_hSkew : BalanceSkew (B := B))
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
        balanceAt B hPack5.z hPack5.x d = 0 := by
  /- TODO (paper C.8.4, Case 2):
     sum (C.15)--(C.20), cancel skew-symmetric opposite terms, obtain
     `4 • (b_xy + b_yz + b_zx) = 0`, then conclude the cycle-sum law. -/
  sorry

/-- Package Case-1 equation data as a C.8.4 branch witness. -/
theorem c8Fallback_fourFiveCycleBranch_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact C8FourFiveCycleBranchHypothesis.ofFourCycle
    hPack4.x hPack4.y hPack4.z hPack4.w
    hPack4.hxy hPack4.hyz hPack4.hzx hPack4.hzw hPack4.hwx
    (c8EqC21_designated_of_equationPack4 (D := D) (B := B) hSkew hPack4)

/-- Package Case-2 equation data as a C.8.4 branch witness. -/
theorem c8Fallback_fourFiveCycleBranch_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact C8FourFiveCycleBranchHypothesis.ofFiveCycle
    hPack5.x hPack5.y hPack5.z hPack5.u hPack5.v
    hPack5.hxy hPack5.hyz hPack5.hzx hPack5.hzu hPack5.huv hPack5.hvx
    (c8EqC21_designated_of_equationPack5 (D := D) (B := B) hSkew hPack5)

theorem c8CycleSumHypothesis_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  refine ⟨hPack4.x, hPack4.y, hPack4.z, hPack4.hxy, hPack4.hyz, hPack4.hzx, ?_⟩
  exact c8EqC21_designated_of_equationPack4 (D := D) (B := B) hSkew hPack4

theorem c8CycleSumHypothesis_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  refine ⟨hPack5.x, hPack5.y, hPack5.z, hPack5.hxy, hPack5.hyz, hPack5.hzx, ?_⟩
  exact c8EqC21_designated_of_equationPack5 (D := D) (B := B) hSkew hPack5

theorem c8CycleSumHypothesis_of_equationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack : C8FallbackEquationPack (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hPack with hPack4 | hPack5
  · rcases hPack4 with ⟨hPack4⟩
    exact c8CycleSumHypothesis_of_equationPack4 (D := D) (B := B) hSkew hPack4
  · rcases hPack5 with ⟨hPack5⟩
    exact c8CycleSumHypothesis_of_equationPack5 (D := D) (B := B) hSkew hPack5

theorem c8Fallback_fourFiveCycleBranch_of_equationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack : C8FallbackEquationPack (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  rcases hPack with hPack4 | hPack5
  · rcases hPack4 with ⟨p4⟩
    exact c8Fallback_fourFiveCycleBranch_of_equationPack4 (D := D) (B := B) hSkew p4
  · rcases hPack5 with ⟨p5⟩
    exact c8Fallback_fourFiveCycleBranch_of_equationPack5 (D := D) (B := B) hSkew p5

noncomputable def c8Fallback_case1_orbitMap
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (d1 : C8Case1OrbitPartitionData X) :
    NProfile V → NProfile V :=
  orbitProfileSum (nu d1.φ) (d1.period - 1)

noncomputable def c8Fallback_case2_orbitMap
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (d2 : C8Case2OrbitPartitionData X) :
    NProfile V → NProfile V :=
  orbitProfileSum (nu d2.φ) (d2.period - 1)

theorem c8Fallback_case1_orbitMap_mem
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X)
    {d : NProfile V} (hd : d ∈ D) :
    c8Fallback_case1_orbitMap (nu := nu) (R := R) d1 d ∈ D := by
  exact orbitProfileSum_mem_of_domainInvariant
    (D := D) hCone nu hInv d1.φ hd (d1.period - 1)

theorem c8Fallback_case2_orbitMap_mem
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X)
    {d : NProfile V} (hd : d ∈ D) :
    c8Fallback_case2_orbitMap (nu := nu) (R := R) d2 d ∈ D := by
  exact orbitProfileSum_mem_of_domainInvariant
    (D := D) hCone nu hInv d2.φ hd (d2.period - 1)

noncomputable def c8Fallback_case1_blockDomainAt
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X)
    (x0 : X) :
    Domain V :=
  orbitBlockDomain D (balanceRule (D := D) B)
    (c8Fallback_case1_orbitMap (nu := nu) (R := R) d1)
    (by
      intro d hd
      exact c8Fallback_case1_orbitMap_mem
        (nu := nu) (R := R) (D := D) hCone hInv d1 hd)
    (orbitSet d1.φ x0)

noncomputable def c8Fallback_case2_blockDomainAt
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X)
    (x0 : X) :
    Domain V :=
  orbitBlockDomain D (balanceRule (D := D) B)
    (c8Fallback_case2_orbitMap (nu := nu) (R := R) d2)
    (by
      intro d hd
      exact c8Fallback_case2_orbitMap_mem
        (nu := nu) (R := R) (D := D) hCone hInv d2 hd)
    (orbitSet d2.φ x0)

structure C8Case1HullWitnessData
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X) where
  x0 : X
  K : AddSubgroup (ZProfile V)
  Kx0 : AddSubgroup (ZProfile V)
  hHullD : IsDivisibleHull (domainImageZ D) K
  hHullBlock0 :
    IsDivisibleHull
      (domainImageZ
        (c8Fallback_case1_blockDomainAt
          (nu := nu) (R := R) (D := D) hCone B hInv d1 x0))
      Kx0
  hHullEq0 : K = Kx0

structure C8Case2HullWitnessData
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X) where
  x0 : X
  K : AddSubgroup (ZProfile V)
  Kx0 : AddSubgroup (ZProfile V)
  hHullD : IsDivisibleHull (domainImageZ D) K
  hHullBlock0 :
    IsDivisibleHull
      (domainImageZ
        (c8Fallback_case2_blockDomainAt
          (nu := nu) (R := R) (D := D) hCone B hInv d2 x0))
      Kx0
  hHullEq0 : K = Kx0

inductive C8Case1WitnessOrbitType (d1 : C8Case1OrbitPartitionData X) (x0 : X) : Prop where
  | threeOrbit : (d1.φ ^ 3) x0 = x0 → C8Case1WitnessOrbitType d1 x0
  | bigOrbit : x0 ∈ orbitSet d1.φ d1.x → C8Case1WitnessOrbitType d1 x0

inductive C8Case2WitnessOrbitType (d2 : C8Case2OrbitPartitionData X) (x0 : X) : Prop where
  | threeOrbit : (d2.φ ^ 3) x0 = x0 → C8Case2WitnessOrbitType d2 x0
  | bigOrbit : x0 ∈ orbitSet d2.φ d2.x → C8Case2WitnessOrbitType d2 x0

theorem c8Fallback_case1_exists_hullWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X) :
    Nonempty
      (C8Case1HullWitnessData
        (nu := nu) (R := R) (D := D) hCone B hInv d1) := by
  /- TODO: apply C.7 with `φ := d1.φ`, `M := d1.period - 1`,
     and package the selected orbit-block hull witness. -/
  sorry

theorem c8Fallback_case2_exists_hullWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X) :
    Nonempty
      (C8Case2HullWitnessData
        (nu := nu) (R := R) (D := D) hCone B hInv d2) := by
  /- TODO: apply C.7 with `φ := d2.φ`, `M := d2.period - 1`,
     and package the selected orbit-block hull witness. -/
  sorry

theorem c8Fallback_case1_classify_witnessOrbit
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1) :
    C8Case1WitnessOrbitType d1 w.x0 := by
  /- TODO: use paper orbit partition for `d1.φ` (all non-big orbits are 3-cycles)
     to classify the C.7 witness orbit. -/
  sorry

theorem c8Fallback_case2_classify_witnessOrbit
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2) :
    C8Case2WitnessOrbitType d2 w.x0 := by
  /- TODO: use paper orbit partition for `d2.φ` (all non-big orbits are 3-cycles)
     to classify the C.7 witness orbit. -/
  sorry

theorem c8Fallback_case1_cycleSum_of_threeOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1)
    (_hthree : (d1.φ ^ 3) w.x0 = w.x0) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  /- TODO: instantiate generalized three-orbit branch lemma using witness-hull
     equality (`w.hHullEq0`) on `orbitSet d1.φ w.x0`. -/
  sorry

theorem c8Fallback_case2_cycleSum_of_threeOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2)
    (_hthree : (d2.φ ^ 3) w.x0 = w.x0) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  /- TODO: instantiate generalized three-orbit branch lemma using witness-hull
     equality (`w.hHullEq0`) on `orbitSet d2.φ w.x0`. -/
  sorry

theorem c8Fallback_case1_equationPack4_of_bigOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1)
    (_hbig : w.x0 ∈ orbitSet d1.φ d1.x) :
    Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) := by
  /- TODO: implement C.8.4 big-orbit branch for Case 1:
     transport from witness block to designated big orbit and derive C.9--C.14. -/
  sorry

theorem c8Fallback_case2_equationPack5_of_bigOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (_hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2)
    (_hbig : w.x0 ∈ orbitSet d2.φ d2.x) :
    Nonempty (C8FallbackEquationPack5 (D := D) (B := B)) := by
  /- TODO: implement C.8.4 big-orbit branch for Case 2:
     transport from witness block to designated big orbit and derive C.15--C.20. -/
  sorry

theorem c8Fallback_case1_branchSplit_of_hullWitness
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
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case1_classify_witnessOrbit
      (nu := nu) (R := R) (D := D) hCone B hInv d1 w with hType
  cases hType with
  | threeOrbit hthree =>
      have hCycle : C8CycleSumHypothesis (D := D) (B := B) :=
        c8Fallback_case1_cycleSum_of_threeOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d1 w hthree
      exact Or.inl (threeCycleBranch_of_cycleSumHypothesis (D := D) (B := B) hCycle)
  | bigOrbit hbig =>
      rcases c8Fallback_case1_equationPack4_of_bigOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d1 w hbig with ⟨p4⟩
      exact Or.inr
        (c8Fallback_fourFiveCycleBranch_of_equationPack
          (D := D) (B := B) hSkew (Or.inl ⟨p4⟩))

theorem c8Fallback_case2_branchSplit_of_hullWitness
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
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case2_classify_witnessOrbit
      (nu := nu) (R := R) (D := D) hCone B hInv d2 w with hType
  cases hType with
  | threeOrbit hthree =>
      have hCycle : C8CycleSumHypothesis (D := D) (B := B) :=
        c8Fallback_case2_cycleSum_of_threeOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d2 w hthree
      exact Or.inl (threeCycleBranch_of_cycleSumHypothesis (D := D) (B := B) hCycle)
  | bigOrbit hbig =>
      rcases c8Fallback_case2_equationPack5_of_bigOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d2 w hbig with ⟨p5⟩
      exact Or.inr
        (c8Fallback_fourFiveCycleBranch_of_equationPack
          (D := D) (B := B) hSkew (Or.inr ⟨p5⟩))

/-- Case-1 partition entrypoint:
construct a hull witness then branch to C.8.3 or C.8.4. -/
theorem c8Fallback_branchSplit_of_case1_partition
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case1_exists_hullWitness
      (nu := nu) (R := R) (D := D)
      hCone B hSkew _hPerfect hInv hNeutralB hR hNE d1 with ⟨w⟩
  exact c8Fallback_case1_branchSplit_of_hullWitness
    (nu := nu) (R := R) (D := D)
    hCone B hSkew _hPerfect hInv hNeutralB hR hNE d1 w

/-- Case-2 partition entrypoint:
construct a hull witness then branch to C.8.3 or C.8.4. -/
theorem c8Fallback_branchSplit_of_case2_partition
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case2_exists_hullWitness
      (nu := nu) (R := R) (D := D)
      hCone B hSkew _hPerfect hInv hNeutralB hR hNE d2 with ⟨w⟩
  exact c8Fallback_case2_branchSplit_of_hullWitness
    (nu := nu) (R := R) (D := D)
    hCone B hSkew _hPerfect hInv hNeutralB hR hNE d2 w

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
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Case1OrbitPartitionData_of_case1 (X := X) hCardGtTwo hCase1 with ⟨d1⟩
  exact c8Fallback_branchSplit_of_case1_partition
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hNE d1

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
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Case2OrbitPartitionData_of_case2 (X := X) hCardGtTwo hCase2 with ⟨d2⟩
  exact c8Fallback_branchSplit_of_case2_partition
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hNE d2

end C8Fallback

end Pivato
