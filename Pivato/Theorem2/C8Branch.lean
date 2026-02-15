import Pivato.Theorem2.C8Seed
import Pivato.Neutrality.Proposition2
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Lemma C.8 branch bridge helpers

This file introduces reusable lemmas for the C.8 branch step:
- orbit-sum fixed-point transport under permutation powers;
- winner transport on profiles fixed by orbit-summation;
- adapters between cycle-sum and branch-split hypotheses.

The full C.8.3/C.8.4 branch derivation theorem will be built on top of these
helpers.
-/

namespace Pivato

section C8Branch

universe uV uX uR

variable {V : Type uV} {X : Type uX} {R : Type uR}

def orbitSet (φ : Equiv.Perm X) (x : X) : Set X :=
  {y | ∃ k : ℕ, (φ ^ k) x = y}

@[simp] lemma mem_orbitSet_iff (φ : Equiv.Perm X) (x y : X) :
    y ∈ orbitSet φ x ↔ ∃ k : ℕ, (φ ^ k) x = y := Iff.rfl

lemma self_mem_orbitSet (φ : Equiv.Perm X) (x : X) :
    x ∈ orbitSet φ x := by
  refine ⟨0, ?_⟩
  simp

def domainImageZ (D : Domain V) : Set (ZProfile V) :=
  {z | ∃ d : NProfile V, d ∈ D ∧ z = toZProfile d}

@[simp] lemma mem_domainImageZ_iff
    (D : Domain V) (z : ZProfile V) :
    z ∈ domainImageZ D ↔ ∃ d : NProfile V, d ∈ D ∧ z = toZProfile d := Iff.rfl

lemma exists_nProfile_of_nsmul_eq_toZProfile
    {n : ℕ} {z : ZProfile V} {d : NProfile V}
    (hn : n ≠ 0)
    (hEq : n • z = toZProfile d) :
    ∃ d' : NProfile V, z = toZProfile d' := by
  have hPos : (0 : ℤ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let d' : NProfile V := z.mapRange Int.toNat (by simp)
  refine ⟨d', ?_⟩
  ext v
  have hEqv : (n : ℤ) * z v = d v := by
    have hEqv' := congrArg (fun f => f v) hEq
    simp [toZProfile] at hEqv'
    exact hEqv'
  have hMulNonneg : 0 ≤ (n : ℤ) * z v := by
    simp [hEqv]
  have hzvNonneg : 0 ≤ z v := by
    rcases (Int.mul_nonneg_iff).1 hMulNonneg with hnn | hnn
    · exact hnn.2
    · exact False.elim ((not_le_of_gt hPos) hnn.1)
  have hzv : ((d' v : ℕ) : ℤ) = z v := by
    simp [d', Int.toNat_of_nonneg hzvNonneg]
  simpa [toZProfile] using hzv.symm

lemma domainImageZ_add_closed
    {D : Domain V}
    (hAdd : DomainAddClosed D) :
    AdditivelyClosed (domainImageZ D) := by
  intro z w hz hw
  rcases hz with ⟨dz, hdz, rfl⟩
  rcases hw with ⟨dw, hdw, rfl⟩
  refine ⟨dz + dw, hAdd hdz hdw, ?_⟩
  simp [toZProfile_add]

lemma domainImageZ_divisible
    {D : Domain V}
    (hDiv : DomainDivisible D) :
    ∀ ⦃z : ZProfile V⦄ ⦃n : ℕ⦄, n ≠ 0 →
      n • z ∈ domainImageZ D → z ∈ domainImageZ D := by
  intro z n hn hz
  rcases hz with ⟨dn, hdn, hEqn⟩
  rcases exists_nProfile_of_nsmul_eq_toZProfile (V := V) hn hEqn with ⟨d', hd'z⟩
  have hnd' : n • d' = dn := by
    apply toZProfile_injective (V := V)
    calc
      toZProfile (n • d') = n • toZProfile d' := by
        simpa using toZProfile_nsmul (n := n) (d := d')
      _ = n • z := by simp [hd'z]
      _ = toZProfile dn := hEqn
  have hnsmulMem : n • d' ∈ D := by simpa [hnd'] using hdn
  refine ⟨d', hDiv hn hnsmulMem, hd'z⟩

lemma isConeSet_domainImageZ
    {D : Domain V}
    (hCone : IsCone D) :
    IsConeSet (domainImageZ D) := by
  refine ⟨domainImageZ_add_closed (D := D) hCone.1, ?_⟩
  intro z n hn hnz
  exact domainImageZ_divisible (D := D) hCone.2 hn hnz

noncomputable def evalIntHom
    [AddCommGroup R]
    (w : V → R) : ZProfile V →+ R :=
  (Finsupp.linearCombination ℤ w).toAddMonoidHom

lemma evalIntHom_toZProfile
    [AddCommGroup R]
    (w : V → R) (d : NProfile V) :
    evalIntHom w (toZProfile d) = evalNat w d := by
  change (Finsupp.linearCombination ℤ w) (toZProfile d) = evalNat w d
  unfold evalNat toZProfile
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index]
  · simp
  · intro a
    simp

lemma domainImageZ_iUnion_eq_of_orbitBlockCover
    {D : Domain V} {F : RuleOn D X}
    (orbitMap : NProfile V → NProfile V)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D)
    (blocks : X → Set X)
    (hCover :
      D = ⋃ x : X, orbitBlockDomain D F orbitMap horbit (blocks x)) :
    domainImageZ D =
      ⋃ x : X,
        domainImageZ (orbitBlockDomain D F orbitMap horbit (blocks x)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨d, hdD, rfl⟩
    have hdCover : d ∈ ⋃ x : X, orbitBlockDomain D F orbitMap horbit (blocks x) := by
      rw [← hCover]
      exact hdD
    rcases Set.mem_iUnion.mp hdCover with ⟨x, hdx⟩
    exact Set.mem_iUnion.mpr ⟨x, ⟨d, hdx, rfl⟩⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨x, hzx⟩
    rcases hzx with ⟨d, hdx, rfl⟩
    exact ⟨d, hdx.1, rfl⟩

lemma orbitProfileSum_succ
    (φ : Equiv.Perm V) (M : ℕ) (d : NProfile V) :
    orbitProfileSum φ (M + 1) d =
      orbitProfileSum φ M d + permuteNProfile (φ ^ (M + 1)) d := by
  simp [orbitProfileSum, Finset.sum_range_succ, add_assoc]

lemma orbitProfileSum_mem_of_powInvariant
    {D : Domain V}
    (hCone : IsCone D)
    (φ : Equiv.Perm V)
    (hInvPow : ∀ k : ℕ, ∀ ⦃d : NProfile V⦄, d ∈ D → permuteNProfile (φ ^ k) d ∈ D)
    {d : NProfile V} (hd : d ∈ D) :
    ∀ M : ℕ, orbitProfileSum φ M d ∈ D := by
  intro M
  induction M with
  | zero =>
      simpa [orbitProfileSum] using hInvPow 0 hd
  | succ M ih =>
      have hTerm : permuteNProfile (φ ^ (M + 1)) d ∈ D := hInvPow (M + 1) hd
      have hStep :
          orbitProfileSum φ (M + 1) d =
            orbitProfileSum φ M d + permuteNProfile (φ ^ (M + 1)) d :=
        orbitProfileSum_succ (φ := φ) (M := M) d
      exact hStep ▸ hCone.1 ih hTerm

lemma orbitProfileSum_fixed_of_pow_eq_one
    (φ : Equiv.Perm V) (M : ℕ) (d : NProfile V)
    (hPow : φ ^ (M + 1) = 1) :
    permuteNProfile φ (orbitProfileSum φ M d) = orbitProfileSum φ M d := by
  have hMap :
      permuteNProfile φ (orbitProfileSum φ M d) =
        Finset.sum (Finset.range (M + 1)) (fun k => permuteNProfile (φ ^ (k + 1)) d) := by
    unfold orbitProfileSum
    simp [permuteNProfile_mul, pow_succ']
  have hShift :
      Finset.sum (Finset.range (M + 1)) (fun k => permuteNProfile (φ ^ (k + 1)) d)
        = Finset.sum (Finset.range M) (fun k => permuteNProfile (φ ^ (k + 1)) d) +
            permuteNProfile (φ ^ (M + 1)) d := by
    simp [Finset.sum_range_succ]
  have hOrig :
      orbitProfileSum φ M d =
        Finset.sum (Finset.range M) (fun k => permuteNProfile (φ ^ (k + 1)) d) +
          permuteNProfile (φ ^ 0) d := by
    unfold orbitProfileSum
    simp [Finset.sum_range_succ']
  have hLast : permuteNProfile (φ ^ (M + 1)) d = permuteNProfile (φ ^ 0) d := by
    simp [hPow]
  calc
    permuteNProfile φ (orbitProfileSum φ M d)
        = Finset.sum (Finset.range (M + 1)) (fun k => permuteNProfile (φ ^ (k + 1)) d) := hMap
    _ = Finset.sum (Finset.range M) (fun k => permuteNProfile (φ ^ (k + 1)) d) +
          permuteNProfile (φ ^ (M + 1)) d := hShift
    _ = Finset.sum (Finset.range M) (fun k => permuteNProfile (φ ^ (k + 1)) d) +
          permuteNProfile (φ ^ 0) d := by simp [hLast]
    _ = orbitProfileSum φ M d := by simp [hOrig]

lemma orbitProfileSum_mem_of_domainInvariant
    {D : Domain V} {X : Type uX}
    (hCone : IsCone D)
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hInv : DomainInvariant nu D)
    (φ : Equiv.Perm X)
    {d : NProfile V} (hd : d ∈ D) (M : ℕ) :
    orbitProfileSum (nu φ) M d ∈ D := by
  refine orbitProfileSum_mem_of_powInvariant
    (D := D) hCone (nu φ) ?_ hd M
  intro k e he
  simpa [MonoidHom.map_pow] using hInv (φ ^ k) he

lemma permuteNProfile_pow_fixed_of_fixed
    (π : Equiv.Perm V) {d : NProfile V}
    (hFix : permuteNProfile π d = d) :
    ∀ k : ℕ, permuteNProfile (π ^ k) d = d := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        permuteNProfile (π ^ (k + 1)) d
            = permuteNProfile π (permuteNProfile (π ^ k) d) := by
                simp [pow_succ', permuteNProfile_mul]
        _ = permuteNProfile π d := by simp [ih]
        _ = d := hFix

lemma winner_orbit_closed_of_fixed_profile
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X}
    {d : NProfile V} (hd : d ∈ D)
    (hFix : permuteNProfile (nu φ) d = d)
    {x : X} (hx : x ∈ balanceRule (D := D) B ⟨d, hd⟩) :
    ∀ k : ℕ, (φ ^ k) x ∈ balanceRule (D := D) B ⟨d, hd⟩ := by
  let hRuleNeutral :
      RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D (balanceRule (D := D) B) :=
    balanceRule_ruleNeutral_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (B := B) hInv hNeutralB
  intro k
  have hFixPowMul :
      permuteNProfile ((nu φ) ^ k) d = d :=
    permuteNProfile_pow_fixed_of_fixed (π := nu φ) hFix k
  have hEq := hRuleNeutral.equivariant (φ ^ k) hd
  have hInPerm :
      (φ ^ k) x ∈ permuteSet (φ ^ k) (balanceRule (D := D) B ⟨d, hd⟩) :=
    ⟨x, hx, rfl⟩
  have hMemAtPerm :
      (φ ^ k) x ∈
        balanceRule (D := D) B
          ⟨permuteNProfile (nu (φ ^ k)) d, hRuleNeutral.domainInvariant (φ ^ k) hd⟩ := by
    exact hEq.symm ▸ hInPerm
  simpa [MonoidHom.map_pow, hFixPowMul] using hMemAtPerm

lemma winner_orbit_closed_of_orbitProfileSum
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X} {M : ℕ} (hPow : φ ^ (M + 1) = 1)
    {d : NProfile V} {hd' : orbitProfileSum (nu φ) M d ∈ D}
    {x : X} (hx : x ∈ balanceRule (D := D) B ⟨orbitProfileSum (nu φ) M d, hd'⟩) :
    ∀ k : ℕ,
      (φ ^ k) x ∈ balanceRule (D := D) B ⟨orbitProfileSum (nu φ) M d, hd'⟩ := by
  have hFix :
      permuteNProfile (nu φ) (orbitProfileSum (nu φ) M d) =
        orbitProfileSum (nu φ) M d := by
    exact orbitProfileSum_fixed_of_pow_eq_one
      (φ := nu φ) (M := M) (d := d) (by simpa [MonoidHom.map_pow] using congrArg nu hPow)
  exact winner_orbit_closed_of_fixed_profile
    (nu := nu) (B := B) hInv hNeutralB
    (hd := hd') (hFix := hFix) (hx := hx)

lemma orbitSet_subset_winners_of_fixed_profile
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {φ : Equiv.Perm X}
    {d : NProfile V} (hd : d ∈ D)
    (hFix : permuteNProfile (nu φ) d = d)
    {x : X} (hx : x ∈ balanceRule (D := D) B ⟨d, hd⟩) :
    orbitSet φ x ⊆ balanceRule (D := D) B ⟨d, hd⟩ := by
  intro y hy
  rcases hy with ⟨k, rfl⟩
  exact winner_orbit_closed_of_fixed_profile
    (nu := nu) (B := B) hInv hNeutralB (hd := hd) (hFix := hFix) (hx := hx) k

lemma balanceAt_eq_zero_of_two_winners
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    {d : NProfile V} (hd : d ∈ D) {x y : X}
    (hx : x ∈ balanceRule (D := D) B ⟨d, hd⟩)
    (hy : y ∈ balanceRule (D := D) B ⟨d, hd⟩) :
    balanceAt B x y d = 0 := by
  have hxyNonneg : (0 : R) ≤ balanceAt B x y d := hx y
  have hyxNonneg : (0 : R) ≤ balanceAt B y x d := hy x
  have hxyNonpos : balanceAt B x y d ≤ 0 := by
    calc
      balanceAt B x y d = -balanceAt B y x d := by
        simpa using hSkew x y d
      _ ≤ 0 := by
        simpa using (neg_nonpos.mpr hyxNonneg)
  exact le_antisymm hxyNonpos hxyNonneg

lemma exists_orbitSet_subset_winners_of_fixed_profile
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    {φ : Equiv.Perm X}
    {d : NProfile V} (hd : d ∈ D)
    (hFix : permuteNProfile (nu φ) d = d) :
    ∃ x : X, orbitSet φ x ⊆ balanceRule (D := D) B ⟨d, hd⟩ := by
  rcases hNE ⟨d, hd⟩ with ⟨x, hx⟩
  exact ⟨x, orbitSet_subset_winners_of_fixed_profile
    (nu := nu) (B := B) hInv hNeutralB (hd := hd) (hFix := hFix) (hx := hx)⟩

theorem claimC82_cover_by_orbitSets_of_neutral_balance
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (hCone : IsCone D)
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (φ : Equiv.Perm X) (M : ℕ) (hPow : φ ^ (M + 1) = 1) :
    D =
      ⋃ x : X,
        orbitBlockDomain D (balanceRule (D := D) B)
          (orbitProfileSum (nu φ) M)
          (by
            intro d hd
            exact orbitProfileSum_mem_of_domainInvariant
              (D := D) hCone nu hInv φ hd M)
          (orbitSet φ x) := by
  let orbitMap : NProfile V → NProfile V := orbitProfileSum (nu φ) M
  have horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv φ hd M
  apply claimC82_cover_by_orbitBlocks
    (D := D) (F := balanceRule (D := D) B)
    orbitMap horbit (blocks := fun x => orbitSet φ x)
  intro d hd
  have hFix :
      permuteNProfile (nu φ) (orbitMap d) = orbitMap d := by
    exact orbitProfileSum_fixed_of_pow_eq_one
      (φ := nu φ) (M := M) (d := d)
      (by simpa [MonoidHom.map_pow] using congrArg nu hPow)
  rcases exists_orbitSet_subset_winners_of_fixed_profile
      (nu := nu) (B := B) hInv hNeutralB hNE
      (hd := horbit hd) (hFix := hFix) with ⟨x, hx⟩
  exact ⟨x, by simpa [orbitMap] using hx⟩

theorem cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (φ : Equiv.Perm X)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitProfileSum (nu φ) 2 d ∈ D)
    {x y z : X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hφx : φ x = z) (hφy : φ y = x) (hφz : φ z = y)
    (K Kblock : AddSubgroup (ZProfile V))
    (hHullD : IsDivisibleHull (domainImageZ D) K)
    (hHullBlock :
      IsDivisibleHull
        (domainImageZ
          (orbitBlockDomain D (balanceRule (D := D) B)
            (orbitProfileSum (nu φ) 2) horbit (orbitSet φ x)))
        Kblock)
    (hHullEq : K = Kblock) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  let orbitMap : NProfile V → NProfile V := orbitProfileSum (nu φ) 2
  have horbit' : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D := by
    intro d hd
    simpa [orbitMap] using (horbit hd)
  let Dblock : Domain V :=
    orbitBlockDomain D (balanceRule (D := D) B) orbitMap horbit' (orbitSet φ x)
  have hHullBlock' : IsDivisibleHull (domainImageZ Dblock) Kblock := by
    simpa [Dblock, orbitMap] using hHullBlock
  let cycleWeight : V → R := fun v =>
    B.bal x y v + B.bal y z v + B.bal z x v
  let ψ : ZProfile V →+ R := evalIntHom cycleWeight
  have hZeroOnBlock : ∀ s, s ∈ domainImageZ Dblock → ψ s = 0 := by
    intro s hs
    rcases hs with ⟨d, hdBlock, rfl⟩
    rcases hdBlock with ⟨hdD, hBlock⟩
    have hxOrbit : x ∈ orbitSet φ x := self_mem_orbitSet φ x
    have hyOrbit : y ∈ orbitSet φ x := by
      refine ⟨2, ?_⟩
      calc
        (φ ^ 2) x = φ (φ x) := by simp [pow_succ']
        _ = φ z := by simp [hφx]
        _ = y := hφz
    have hxWin :
        x ∈ balanceRule (D := D) B ⟨orbitMap d, horbit' hdD⟩ :=
      hBlock hxOrbit
    have hyWin :
        y ∈ balanceRule (D := D) B ⟨orbitMap d, horbit' hdD⟩ :=
      hBlock hyOrbit
    have hxyZero :
        balanceAt B x y (orbitMap d) = 0 :=
      balanceAt_eq_zero_of_two_winners
        (D := D) B hSkew (hd := horbit' hdD) hxWin hyWin
    have hTerm1 :
        balanceAt B x y (permuteNProfile (nu φ) d) =
          balanceAt B y z d := by
      have hBase :=
        balanceAt_permute_of_balanceNeutral
          (mu := MonoidHom.id (Equiv.Perm X))
          (nu := nu) (B := B) hNeutralB φ y z d
      simpa [hφy, hφz] using hBase
    have hφ2z : (φ ^ 2) z = x := by
      calc
        (φ ^ 2) z = φ (φ z) := by simp [pow_succ']
        _ = φ y := by simp [hφz]
        _ = x := hφy
    have hφ2x : (φ ^ 2) x = y := by
      calc
        (φ ^ 2) x = φ (φ x) := by simp [pow_succ']
        _ = φ z := by simp [hφx]
        _ = y := hφz
    have hTerm2 :
        balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) =
          balanceAt B z x d := by
      have hBase :=
        balanceAt_permute_of_balanceNeutral
          (mu := MonoidHom.id (Equiv.Perm X))
          (nu := nu) (B := B) hNeutralB (φ ^ 2) z x d
      simpa [MonoidHom.map_pow, hφ2z, hφ2x] using hBase
    have hExpand :
        balanceAt B x y (orbitMap d) =
          balanceAt B x y d +
            balanceAt B x y (permuteNProfile (nu φ) d) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) := by
      have hOrbit :
          orbitMap d =
            d + (permuteNProfile (nu φ) d +
              permuteNProfile ((nu φ) ^ 2) d) := by
        unfold orbitMap orbitProfileSum
        simp [Finset.sum_range_succ, add_assoc]
      calc
        balanceAt B x y (orbitMap d)
            = balanceAt B x y
                (d + permuteNProfile (nu φ) d + permuteNProfile ((nu φ) ^ 2) d) := by
                  simpa [add_assoc] using congrArg (balanceAt B x y) hOrbit
        _ = balanceAt B x y (d + permuteNProfile (nu φ) d) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) := by
                simpa [add_assoc] using
                  (balanceAt_add (B := B) (x := x) (y := y)
                    (d := d + permuteNProfile (nu φ) d)
                    (e := permuteNProfile ((nu φ) ^ 2) d))
        _ = (balanceAt B x y d + balanceAt B x y (permuteNProfile (nu φ) d)) +
              balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) := by
                simpa [add_assoc] using
                  (congrArg (fun t =>
                    t + balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d))
                    (balanceAt_add (B := B) (x := x) (y := y)
                      (d := d) (e := permuteNProfile (nu φ) d)))
        _ = balanceAt B x y d +
              balanceAt B x y (permuteNProfile (nu φ) d) +
                balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) := by
                simp [add_assoc]
    have hCycleD :
        balanceAt B x y d + balanceAt B y z d + balanceAt B z x d = 0 := by
      calc
        balanceAt B x y d + balanceAt B y z d + balanceAt B z x d
            = balanceAt B x y d +
                balanceAt B x y (permuteNProfile (nu φ) d) +
                  balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) := by
                    simp [hTerm1, hTerm2, add_assoc]
        _ = balanceAt B x y (orbitMap d) := hExpand.symm
        _ = 0 := hxyZero
    have hPsiD :
        ψ (toZProfile d) =
          balanceAt B x y d + balanceAt B y z d + balanceAt B z x d := by
      change evalIntHom cycleWeight (toZProfile d) = _
      rw [evalIntHom_toZProfile]
      unfold cycleWeight
      simp [balanceAt, evalNat, add_assoc]
    simpa [hPsiD] using hCycleD
  have hZeroOnKblock :
      ∀ a, a ∈ Kblock → ψ a = 0 :=
    lemmaC5 (φ := ψ) (S := domainImageZ Dblock) (K := Kblock)
      hHullBlock' hZeroOnBlock
  refine ⟨x, y, z, hxy, hyz, hzx, ?_⟩
  intro d hdD
  have hzD : toZProfile d ∈ domainImageZ D := ⟨d, hdD, rfl⟩
  have hzK : toZProfile d ∈ K := hHullD.2.1 hzD
  have hzKblock : toZProfile d ∈ Kblock := by
    simpa [hHullEq] using hzK
  have hPsi0 : ψ (toZProfile d) = 0 := hZeroOnKblock (toZProfile d) hzKblock
  have hPsiD :
      ψ (toZProfile d) =
        balanceAt B x y d + balanceAt B y z d + balanceAt B z x d := by
    change evalIntHom cycleWeight (toZProfile d) = _
    rw [evalIntHom_toZProfile]
    unfold cycleWeight
    simp [balanceAt, evalNat, add_assoc]
  simpa [hPsiD] using hPsi0

theorem exists_orbitSet_hull_eq_of_neutral_balance
    [Finite X] [Nonempty X] [DecidableEq X]
    [AddCommMonoid R] [LinearOrder R] [Zero R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (nu : Equiv.Perm X →* Equiv.Perm V)
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (φ : Equiv.Perm X) (M : ℕ) (hPow : φ ^ (M + 1) = 1)
    (K : AddSubgroup (ZProfile V))
    (Kx : X → AddSubgroup (ZProfile V))
    (hHullD : IsDivisibleHull (domainImageZ D) K)
    (hHullBlocks :
      ∀ x : X,
        IsDivisibleHull
          (domainImageZ
            (orbitBlockDomain D (balanceRule (D := D) B)
              (orbitProfileSum (nu φ) M)
              (by
                intro d hd
                exact orbitProfileSum_mem_of_domainInvariant
                  (D := D) hCone nu hInv φ hd M)
              (orbitSet φ x)))
          (Kx x)) :
    ∃ x : X, K = Kx x := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let orbitMap : NProfile V → NProfile V := orbitProfileSum (nu φ) M
  have horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv φ hd M
  let S : X → Set (ZProfile V) := fun x =>
    domainImageZ (orbitBlockDomain D (balanceRule (D := D) B) orbitMap horbit (orbitSet φ x))
  have hCover :
      D = ⋃ x : X,
        orbitBlockDomain D (balanceRule (D := D) B) orbitMap horbit (orbitSet φ x) := by
    simpa [orbitMap, horbit] using
      (claimC82_cover_by_orbitSets_of_neutral_balance
        (D := D) hCone nu B hInv hNeutralB hNE φ M hPow)
  have hUnion :
      domainImageZ D = ⋃ x : X, S x := by
    simpa [S] using
      (domainImageZ_iUnion_eq_of_orbitBlockCover
        (D := D) (F := balanceRule (D := D) B) orbitMap horbit
        (blocks := fun x => orbitSet φ x) hCover)
  have hConeBlock : ∀ x : X,
      IsCone (orbitBlockDomain D (balanceRule (D := D) B) orbitMap horbit (orbitSet φ x)) := by
    intro x
    exact claimC81_orbitBlock_isCone
      (D := D) (F := balanceRule (D := D) B)
      hCone hR hNE orbitMap horbit
      (by
        intro d e
        simpa [orbitMap] using
          (orbitProfileSum_add (φ := nu φ) (M := M) d e))
      (by
        intro n d
        simpa [orbitMap] using
          (orbitProfileSum_nsmul (φ := nu φ) (M := M) n d))
      (orbitSet φ x)
  have hConeS : ∀ x : X, IsConeSet (S x) := by
    intro x
    exact isConeSet_domainImageZ (D := orbitBlockDomain D (balanceRule (D := D) B)
      orbitMap horbit (orbitSet φ x)) (hConeBlock x)
  have hHullS : ∀ x : X, IsDivisibleHull (S x) (Kx x) := by
    intro x
    simpa [S, orbitMap, horbit] using hHullBlocks x
  have hAddClosedUnion : AdditivelyClosed (⋃ x : X, S x) := by
    simpa [hUnion] using (domainImageZ_add_closed (D := D) hCone.1)
  have hHullUnion : IsDivisibleHull (⋃ x : X, S x) K := by
    simpa [hUnion] using hHullD
  exact lemmaC7
    (A := ZProfile V) (ι := X)
    (S := S) (K := K) (Kᵢ := Kx)
    hHullUnion hHullS hConeS hAddClosedUnion

end C8Branch

end Pivato
