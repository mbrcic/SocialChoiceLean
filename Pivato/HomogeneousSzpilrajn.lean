import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Order.Zorn

/-!
# Homogeneous Szpilrajn lemma (additive form)

This file formalizes the additive-group form used in Pivato's appendix:
on a torsion-free abelian group, every homogeneous partial order extends
to a homogeneous linear order.
-/

open Set

namespace Pivato

section AddGroupConeExtension

variable {G : Type*} [AddCommGroup G]

/-- The set obtained by adjoining a generator `a` to an additive cone `C`. -/
def adjoinCarrier (C : AddGroupCone G) (a : G) : Set G :=
  {x | ∃ c ∈ (C : Set G), ∃ n : ℕ, x = c + n • a}

/-- Pointedness property for a subset of an additive group. -/
def IsPointed (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S → x = 0

lemma mem_adjoinCarrier_of_mem {C : AddGroupCone G} {a x : G} (hx : x ∈ C) :
    x ∈ adjoinCarrier C a := by
  refine ⟨x, hx, 0, by simp⟩

lemma subset_adjoinCarrier (C : AddGroupCone G) (a : G) : (C : Set G) ⊆ adjoinCarrier C a := by
  intro x hx
  exact mem_adjoinCarrier_of_mem hx

lemma mem_adjoinCarrier_self (C : AddGroupCone G) (a : G) : a ∈ adjoinCarrier C a := by
  refine ⟨0, C.zero_mem, 1, ?_⟩
  simp

/-- Turn `adjoinCarrier C a` into an additive cone, provided pointedness. -/
def adjoinCone (C : AddGroupCone G) (a : G) (hpoint : IsPointed (adjoinCarrier C a)) :
    AddGroupCone G where
  carrier := adjoinCarrier C a
  zero_mem' := by
    exact mem_adjoinCarrier_of_mem (C := C) (a := a) C.zero_mem
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨cx, hcx, nx, rfl⟩
    rcases hy with ⟨cy, hcy, ny, rfl⟩
    refine ⟨cx + cy, C.add_mem hcx hcy, nx + ny, ?_⟩
    simp [add_assoc, add_left_comm, add_nsmul]
  eq_zero_of_mem_of_neg_mem' := by
    intro x hx hnegx
    exact hpoint hx hnegx

/-- Supremum (as union of carriers) of a nonempty chain of additive cones. -/
def chainSupCone (c : Set (AddGroupCone G)) (hc : IsChain (· ≤ ·) c)
    (y : AddGroupCone G) (hy : y ∈ c) : AddGroupCone G where
  carrier := {x | ∃ D ∈ c, x ∈ (D : Set G)}
  zero_mem' := by
    exact ⟨y, hy, y.zero_mem⟩
  add_mem' := by
    intro x z hx hz
    rcases hx with ⟨Dx, hDx, hxDx⟩
    rcases hz with ⟨Dz, hDz, hzDz⟩
    rcases hc.total hDx hDz with hDxz | hDzx
    · exact ⟨Dz, hDz, Dz.add_mem (hDxz hxDx) hzDz⟩
    · exact ⟨Dx, hDx, Dx.add_mem hxDx (hDzx hzDz)⟩
  eq_zero_of_mem_of_neg_mem' := by
    intro x hx hnegx
    rcases hx with ⟨Dx, hDx, hxDx⟩
    rcases hnegx with ⟨Dz, hDz, hnegxDz⟩
    rcases hc.total hDx hDz with hDxz | hDzx
    · exact eq_zero_of_mem_of_neg_mem (hDxz hxDx) hnegxDz
    · exact eq_zero_of_mem_of_neg_mem hxDx (hDzx hnegxDz)

lemma le_chainSupCone (c : Set (AddGroupCone G)) (hc : IsChain (· ≤ ·) c)
    (y : AddGroupCone G) (hy : y ∈ c) :
    y ≤ chainSupCone c hc y hy := by
  intro x hx
  exact ⟨y, hy, hx⟩

/-- Zorn: every additive cone extends to a maximal one. -/
theorem exists_maximal_cone_extension (C0 : AddGroupCone G) :
    ∃ M : AddGroupCone G, C0 ≤ M ∧ Maximal (fun D : AddGroupCone G => C0 ≤ D) M := by
  let S : Set (AddGroupCone G) := {D | C0 ≤ D}
  have hchain :
      ∀ c ⊆ S, IsChain (· ≤ ·) c →
        ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    refine ⟨chainSupCone c hc y hy, ?_, ?_⟩
    · exact (hcS hy).trans (le_chainSupCone c hc y hy)
    · intro z hz x hx
      exact ⟨z, hz, hx⟩
  have hC0 : C0 ∈ S := by
    intro x hx
    exact hx
  obtain ⟨M, hC0M, hmax⟩ := zorn_le_nonempty₀ S hchain C0 hC0
  exact ⟨M, hC0M, hmax⟩

lemma exists_pos_nat_neg_nsmul_mem_of_not_pointed_adjoin
    {C : AddGroupCone G} {a : G}
    (hnot : ¬ IsPointed (adjoinCarrier C a)) :
    ∃ n : ℕ, 0 < n ∧ -(n • a) ∈ C := by
  by_contra h
  apply hnot
  intro x hx hnegx
  rcases hx with ⟨c1, hc1, n1, hxEq⟩
  rcases hnegx with ⟨c2, hc2, n2, hnegEq⟩
  have hsum : c1 + c2 + (n1 + n2) • a = 0 := by
    calc
      c1 + c2 + (n1 + n2) • a = (c1 + n1 • a) + (c2 + n2 • a) := by
        simp [add_assoc, add_left_comm, add_nsmul]
      _ = (c1 + n1 • a) + (-x) := by simp [hnegEq]
      _ = x + (-x) := by simp [hxEq]
      _ = 0 := by simp
  have hnegMem : -((n1 + n2) • a) ∈ C := by
    have hEq : c1 + c2 = -((n1 + n2) • a) := eq_neg_of_add_eq_zero_left hsum
    have hc12 : c1 + c2 ∈ C := C.add_mem hc1 hc2
    simpa [hEq] using hc12
  have hNotPos : ¬ 0 < n1 + n2 := by
    intro hpos
    exact h ⟨n1 + n2, hpos, hnegMem⟩
  have hzeroNat : n1 + n2 = 0 := Nat.eq_zero_of_not_pos hNotPos
  rcases Nat.add_eq_zero_iff.mp hzeroNat with ⟨hn1, hn2⟩
  have hxC : x ∈ C := by
    simpa [hxEq, hn1] using hc1
  have hnegxC : -x ∈ C := by
    simpa [hnegEq, hn2] using hc2
  exact eq_zero_of_mem_of_neg_mem hxC hnegxC

lemma not_pointed_adjoin_of_not_mem
    {C0 M : AddGroupCone G} (hC0M : C0 ≤ M) (hmax : Maximal (fun D : AddGroupCone G => C0 ≤ D) M)
    {a : G} (ha : a ∉ M) :
    ¬ IsPointed (adjoinCarrier M a) := by
  intro hpoint
  let D : AddGroupCone G := adjoinCone M a hpoint
  have hMD : M ≤ D := subset_adjoinCarrier M a
  have hC0D : C0 ≤ D := hC0M.trans hMD
  have hDM : D ≤ M := hmax.le_of_ge hC0D hMD
  have haD : a ∈ D := mem_adjoinCarrier_self M a
  exact ha (hDM haD)

/-- A maximal cone in a torsion-free group is total. -/
theorem maximal_cone_mem_or_neg_mem
    [IsAddTorsionFree G] {C0 M : AddGroupCone G}
    (hC0M : C0 ≤ M) (hmax : Maximal (fun D : AddGroupCone G => C0 ≤ D) M) (a : G) :
    a ∈ M ∨ -a ∈ M := by
  by_cases ha : a ∈ M
  · exact Or.inl ha
  by_cases hna : -a ∈ M
  · exact Or.inr hna
  have hnotPlus : ¬ IsPointed (adjoinCarrier M a) :=
    not_pointed_adjoin_of_not_mem hC0M hmax ha
  have hnotMinus : ¬ IsPointed (adjoinCarrier M (-a)) :=
    not_pointed_adjoin_of_not_mem hC0M hmax hna
  obtain ⟨m, hmpos, hmneg⟩ := exists_pos_nat_neg_nsmul_mem_of_not_pointed_adjoin hnotPlus
  obtain ⟨n, hnpos, hnneg⟩ := exists_pos_nat_neg_nsmul_mem_of_not_pointed_adjoin hnotMinus
  have hposMul : n • a ∈ M := by
    simpa [neg_nsmul, neg_neg] using hnneg
  have hmul : (m * n) • a ∈ M := by
    simpa [mul_nsmul', Nat.mul_comm] using nsmul_mem hposMul m
  have hnegMul : -((m * n) • a) ∈ M := by
    have : n • (-(m • a)) ∈ M := nsmul_mem hmneg n
    have htmp : -(n • m • a) ∈ M := by
      simpa [neg_nsmul] using this
    have hEqnm : n • m • a = (m * n) • a := by
      simpa [Nat.mul_comm] using (mul_nsmul' a n m).symm
    simpa [hEqnm] using htmp
  have hzeroMul : (m * n) • a = 0 := eq_zero_of_mem_of_neg_mem hmul hnegMul
  have hmn_ne_zero : m * n ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hmpos) (Nat.ne_of_gt hnpos)
  have ha0 : a = 0 := by
    have hEq : (m * n) • a = (m * n) • (0 : G) := by simpa using hzeroMul
    exact (nsmul_right_injective hmn_ne_zero) hEq
  exact False.elim (ha (ha0 ▸ M.zero_mem))

/-- Cone form of the homogeneous Szpilrajn lemma. -/
theorem homogeneous_szpilrajn_cone
    [IsAddTorsionFree G] (C0 : AddGroupCone G) :
    ∃ M : AddGroupCone G, C0 ≤ M ∧ HasMemOrNegMem M := by
  obtain ⟨M, hC0M, hmax⟩ := exists_maximal_cone_extension C0
  refine ⟨M, hC0M, ?_⟩
  refine ⟨?_⟩
  intro a
  exact maximal_cone_mem_or_neg_mem hC0M hmax a

end AddGroupConeExtension

section RelationForm

variable {G : Type*} [AddCommGroup G]

/-- Homogeneity in difference form. -/
def Homogeneous (r : G → G → Prop) : Prop :=
  ∀ x y, r x y ↔ r 0 (y - x)

/-- Positive cone associated to a homogeneous relation. -/
def coneOfHomogeneous (r : G → G → Prop) [IsPartialOrder G r] (hr : Homogeneous r) :
    AddGroupCone G where
  carrier := {a : G | r 0 a}
  zero_mem' := by simpa using (refl (r := r) 0)
  add_mem' := by
    intro a b ha hb
    have hab : r a (a + b) := by
      exact (hr a (a + b)).2 (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb)
    exact trans ha hab
  eq_zero_of_mem_of_neg_mem' := by
    intro a ha hna
    have ha0 : r a 0 := by
      exact (hr a 0).2 (by simpa using hna)
    exact antisymm ha0 ha

/-- Homogeneous Szpilrajn lemma (relation form). -/
  theorem homogeneous_szpilrajn
      [IsAddTorsionFree G]
      (r : G → G → Prop) [IsPartialOrder G r] (hr : Homogeneous r) :
      ∃ s : G → G → Prop, IsLinearOrder G s ∧ r ≤ s ∧ Homogeneous s := by
  classical
  let C0 : AddGroupCone G := coneOfHomogeneous r hr
  obtain ⟨M, hC0M, _htotal⟩ := homogeneous_szpilrajn_cone C0
  letI : DecidablePred (fun x : G => x ∈ M) := Classical.decPred _
  letI : LinearOrder G := LinearOrder.mkOfAddGroupCone M
  refine ⟨(· ≤ ·), inferInstance, ?_, ?_⟩
  · intro x y hxy
    have hmem : y - x ∈ M := hC0M ((hr x y).1 hxy)
    simpa [PartialOrder.mkOfAddGroupCone_le_iff] using hmem
  · intro x y
    simp [PartialOrder.mkOfAddGroupCone_le_iff, sub_eq_add_neg]

end RelationForm

end Pivato
