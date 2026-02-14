import Pivato.Theorem1.Cones
import Pivato.Theorem1.DomainPurity
import Pivato.AppendixB
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Order.Extension.Linear

/-!
# Theorem 1 core: pairwise difference cones and quotient orders

This file introduces:
- `P_{x,y}` as a difference-cone candidate in `Z^{<V>}`,
- its induced homogeneous relation,
- symmetric-kernel and quotient-subgroup construction,
- pairwise quotient partial orders and linearized pairwise maps.
-/

namespace Pivato

instance linearExtensionAddCommGroup (A : Type*) [AddCommGroup A] :
    AddCommGroup (LinearExtension A) := by
  delta LinearExtension
  infer_instance

section PairwiseCones

variable {V X : Type*} {D : Domain V}

/-- Pairwise difference cone candidate: `P_{x,y} = C_x - C_y`. -/
def pairwiseDifferenceCone (F : RuleOn D X) (x y : X) : Set (ZProfile V) :=
  {z | ∃ cx cy : NProfile V,
      cx ∈ winnerCone F x ∧
      cy ∈ winnerCone F y ∧
      z = toZProfile cx - toZProfile cy}

/-- Homogeneous relation induced by `P_{x,y}` in conoid form. -/
def pairwiseRel (F : RuleOn D X) (x y : X) : ZProfile V → ZProfile V → Prop :=
  relOfConoid (pairwiseDifferenceCone F x y)

lemma pairwiseRel_homogeneous (F : RuleOn D X) (x y : X) :
    Homogeneous (pairwiseRel F x y) :=
  relOfConoid_homogeneous _

/-- Symmetric-kernel candidate for the pairwise relation. -/
def pairwiseKernelSet (F : RuleOn D X) (x y : X) : Set (ZProfile V) :=
  {z | symmPart (pairwiseRel F x y) z 0}

lemma pairwiseDifferenceCone_add_closed
    {F : RuleOn D X} (hR : Reinforcement D F) (x y : X) :
    AdditivelyClosed (pairwiseDifferenceCone F x y) := by
  intro a b ha hb
  rcases ha with ⟨cx₁, cy₁, hcx₁, hcy₁, rfl⟩
  rcases hb with ⟨cx₂, cy₂, hcx₂, hcy₂, rfl⟩
  refine ⟨cx₁ + cx₂, cy₁ + cy₂, ?_, ?_, ?_⟩
  · exact (winnerCone_add_closed_of_reinforcement (F := F) hR x) hcx₁ hcx₂
  · exact (winnerCone_add_closed_of_reinforcement (F := F) hR y) hcy₁ hcy₂
  · simp [toZProfile_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma pairwiseDifferenceCone_zero_mem
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F) (x y : X) :
    (0 : ZProfile V) ∈ pairwiseDifferenceCone F x y := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · exact winnerCone_zero_of_generalAbstention (F := F) hD hA x
  · exact winnerCone_zero_of_generalAbstention (F := F) hD hA y
  · simp [toZProfile_zero]

lemma pairwiseDifferenceCone_isPreorderConoid
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    IsPreorderConoid (pairwiseDifferenceCone F x y) := by
  refine ⟨pairwiseDifferenceCone_add_closed (F := F) hR x y, ?_⟩
  exact pairwiseDifferenceCone_zero_mem (F := F) hD hA x y

lemma pairwiseRel_isPreorderRel
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    IsPreorderRel (pairwiseRel F x y) := by
  have hCone : IsPreorderConoid (positiveConoid (pairwiseRel F x y)) := by
    simpa [pairwiseRel, positiveConoid_relOfConoid] using
      (pairwiseDifferenceCone_isPreorderConoid (F := F) hD hA hR x y)
  exact (lemmaB1a_preorder (r := pairwiseRel F x y)
    (pairwiseRel_homogeneous (F := F) x y)).2 hCone

lemma pairwiseRel_refl
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    Reflexive (pairwiseRel F x y) :=
  (pairwiseRel_isPreorderRel (F := F) hD hA hR x y).1

lemma pairwiseRel_trans
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    Transitive (pairwiseRel F x y) :=
  (pairwiseRel_isPreorderRel (F := F) hD hA hR x y).2

def pairwiseKernelSubgroup
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) : AddSubgroup (ZProfile V) where
  carrier := {z | z ∈ pairwiseDifferenceCone F x y ∧ -z ∈ pairwiseDifferenceCone F x y}
  zero_mem' := by
    exact ⟨pairwiseDifferenceCone_zero_mem (F := F) hD hA x y, by simpa using
      (pairwiseDifferenceCone_zero_mem (F := F) hD hA x y)⟩
  add_mem' := by
    intro z w hz hw
    refine ⟨?_, ?_⟩
    · exact (pairwiseDifferenceCone_add_closed (F := F) hR x y) hz.1 hw.1
    · have hneg : -z + -w ∈ pairwiseDifferenceCone F x y :=
        (pairwiseDifferenceCone_add_closed (F := F) hR x y) hz.2 hw.2
      simpa [add_comm, add_left_comm, add_assoc, neg_add] using hneg
  neg_mem' := by
    intro z hz
    refine ⟨hz.2, ?_⟩
    simpa using hz.1

lemma mem_pairwiseKernelSubgroup_iff
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) {x y : X} {z : ZProfile V} :
    z ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y ↔
      symmPart (pairwiseRel F x y) z 0 := by
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using hz.2
    · simpa [pairwiseRel, relOfConoid] using hz.1
  · intro hz
    refine ⟨?_, ?_⟩
    · simpa [pairwiseRel, relOfConoid] using hz.2
    · simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using hz.1

lemma mem_pairwiseKernelSet_iff
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) {x y : X} {z : ZProfile V} :
    z ∈ pairwiseKernelSet F x y ↔
      z ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := by
  simpa [pairwiseKernelSet] using
    (mem_pairwiseKernelSubgroup_iff (F := F) hD hA hR (x := x) (y := y) (z := z)).symm

lemma mem_pairwiseDifferenceCone_swap_iff
    {F : RuleOn D X} {x y : X} {z : ZProfile V} :
    z ∈ pairwiseDifferenceCone F y x ↔ -z ∈ pairwiseDifferenceCone F x y := by
  constructor
  · intro hz
    rcases hz with ⟨cy, cx, hcy, hcx, hzEq⟩
    refine ⟨cx, cy, hcx, hcy, ?_⟩
    calc
      -z = -(toZProfile cy - toZProfile cx) := by simp [hzEq]
      _ = toZProfile cx - toZProfile cy := by
        simp [sub_eq_add_neg, add_comm]
  · intro hz
    rcases hz with ⟨cx, cy, hcx, hcy, hzEq⟩
    refine ⟨cy, cx, hcy, hcx, ?_⟩
    have hneg : z = -(toZProfile cx - toZProfile cy) := by
      simpa using congrArg Neg.neg hzEq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg

lemma toZProfile_mem_pairwiseDifferenceCone_of_winner
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    {x y : X} {d : NProfile V}
    (hxd : d ∈ winnerCone F x) :
    toZProfile d ∈ pairwiseDifferenceCone F x y := by
  refine ⟨d, 0, hxd, winnerCone_zero_of_generalAbstention (F := F) hD hA y, ?_⟩
  simp [toZProfile_zero, sub_eq_add_neg]

lemma toZProfile_mem_pairwiseDifferenceCone_of_nsmul_winner
    {F : RuleOn D X} (hPure : DomainPure D)
    (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    {x y : X} {d : NProfile V} {n : ℕ} (hn : n ≠ 0)
    (hxn : n • d ∈ winnerCone F x) :
    toZProfile d ∈ pairwiseDifferenceCone F x y := by
  have hxd : d ∈ winnerCone F x :=
    winnerCone_divisible_of_domainDivisible (F := F) hPure hR hNE x hn hxn
  exact toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA hxd

lemma toZProfile_mem_pairwiseKernelSubgroup_of_nsmul_winner_winner
    {F : RuleOn D X} (hPure : DomainPure D)
    (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    {x y : X} {d : NProfile V} {n : ℕ} (hn : n ≠ 0)
    (hxn : n • d ∈ winnerCone F x)
    (hyn : n • d ∈ winnerCone F y) :
    toZProfile d ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := by
  have hxd : d ∈ winnerCone F x :=
    winnerCone_divisible_of_domainDivisible (F := F) hPure hR hNE x hn hxn
  have hyd : d ∈ winnerCone F y :=
    winnerCone_divisible_of_domainDivisible (F := F) hPure hR hNE y hn hyn
  have hxyMem : toZProfile d ∈ pairwiseDifferenceCone F x y :=
    toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA hxd
  have hyxMem : toZProfile d ∈ pairwiseDifferenceCone F y x :=
    toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA hyd
  have hnegMem : -toZProfile d ∈ pairwiseDifferenceCone F x y :=
    (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := x) (y := y)
      (z := toZProfile d)).1 hyxMem
  exact ⟨hxyMem, hnegMem⟩

lemma neg_toZProfile_not_mem_pairwiseDifferenceCone_of_winner_loser
    {F : RuleOn D X}
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V} {hd : d ∈ D}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    -toZProfile d ∉ pairwiseDifferenceCone F x y := by
  intro hnegMem
  rcases hnegMem with ⟨cx, cy, hcx, hcy, hEq⟩
  rcases hcx with ⟨hcxD, hxcx⟩
  rcases hcy with ⟨hcyD, hycy⟩
  have hcxEq : toZProfile cx - toZProfile cy = -toZProfile d := hEq.symm
  have hcxAdd : toZProfile cx = -toZProfile d + toZProfile cy :=
    (sub_eq_iff_eq_add).1 hcxEq
  have hcyEqZ : toZProfile cy = toZProfile (cx + d) := by
    ext v
    have hv : (cx v : ℤ) = (cy v : ℤ) - (d v : ℤ) := by
      simpa [sub_eq_add_neg, toZProfile_apply, add_comm, add_left_comm, add_assoc] using
        congrArg (fun f => f v) hcxAdd
    have hv' : (cy v : ℤ) = (cx v : ℤ) + (d v : ℤ) := by
      exact ((eq_sub_iff_add_eq).1 hv).symm
    simpa [toZProfile_apply, Nat.cast_add, add_comm, add_left_comm, add_assoc] using hv'
  have hcyEq : cy = d + cx := by
    simpa [add_comm] using (toZProfile_injective (V := V)) hcyEqZ
  have hinter : (F ⟨d, hd⟩ ∩ F ⟨cx, hcxD⟩).Nonempty := ⟨x, hxd, hxcx⟩
  have hsum : d + cx ∈ D := hR.1 hd hcxD hinter
  have hEqR :
      F ⟨d + cx, hsum⟩ = F ⟨d, hd⟩ ∩ F ⟨cx, hcxD⟩ :=
    hR.2 hd hcxD hsum hinter
  have hynotSum : y ∉ F ⟨d + cx, hsum⟩ := by
    intro hysum
    have hyInter : y ∈ F ⟨d, hd⟩ ∩ F ⟨cx, hcxD⟩ := by
      simpa [hEqR] using hysum
    exact hynotd hyInter.1
  have hynotCy' : y ∉ F ⟨cy, hcyEq ▸ hsum⟩ := by
    simpa [hcyEq] using hynotSum
  have hynotCy : y ∉ F ⟨cy, hcyD⟩ := by
    intro hy
    exact hynotCy' ((wins_proof_irrel (F := F) (x := y) (d := cy)
      (hd₁ := hcyEq ▸ hsum) (hd₂ := hcyD)).2 hy)
  exact hynotCy hycy

lemma pairwiseRel_zero_toZProfile_of_winner
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    {x y : X} {d : NProfile V}
    (hxd : d ∈ winnerCone F x) :
    pairwiseRel F x y 0 (toZProfile d) := by
  simpa [pairwiseRel, relOfConoid] using
    (toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA hxd)

lemma not_pairwiseRel_toZProfile_zero_of_winner_loser
    {F : RuleOn D X}
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V} {hd : d ∈ D}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    ¬ pairwiseRel F x y (toZProfile d) 0 := by
  simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using
    (neg_toZProfile_not_mem_pairwiseDifferenceCone_of_winner_loser
      (F := F) hR hxd hynotd)

lemma pairwiseRel_toZProfile_zero_of_winner_swapped
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    {x y : X} {d : NProfile V}
    (hyd : d ∈ winnerCone F y) :
    pairwiseRel F x y (toZProfile d) 0 := by
  have hyx : toZProfile d ∈ pairwiseDifferenceCone F y x :=
    toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA hyd
  have hxy : -toZProfile d ∈ pairwiseDifferenceCone F x y :=
    (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := x) (y := y)
      (z := toZProfile d)).1 hyx
  simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using hxy

lemma not_pairwiseRel_zero_toZProfile_of_winner_loser_swapped
    {F : RuleOn D X} (hR : Reinforcement D F)
    {x y : X} {d : NProfile V} {hd : d ∈ D}
    (hyd : y ∈ F ⟨d, hd⟩)
    (hxnotd : x ∉ F ⟨d, hd⟩) :
    ¬ pairwiseRel F x y 0 (toZProfile d) := by
  intro hxy
  have hxyMem : toZProfile d ∈ pairwiseDifferenceCone F x y := by
    simpa [pairwiseRel, relOfConoid] using hxy
  have hyxNegMem : -toZProfile d ∈ pairwiseDifferenceCone F y x :=
    (mem_pairwiseDifferenceCone_swap_iff (F := F) (x := y) (y := x)
      (z := toZProfile d)).1 hxyMem
  have hyx : pairwiseRel F y x (toZProfile d) 0 := by
    simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using hyxNegMem
  exact (not_pairwiseRel_toZProfile_zero_of_winner_loser (F := F) hR hyd hxnotd) hyx

abbrev PairwiseQuotient
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :=
  (ZProfile V) ⧸ pairwiseKernelSubgroup (F := F) hD hA hR x y

def pairwiseQuotientCone
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    Set (PairwiseQuotient (F := F) hD hA hR x y) :=
  {q | ∃ z : ZProfile V,
      z ∈ pairwiseDifferenceCone F x y ∧
      (QuotientAddGroup.mk' (pairwiseKernelSubgroup (F := F) hD hA hR x y) z) = q}

def pairwiseQuotientRel
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    PairwiseQuotient (F := F) hD hA hR x y →
      PairwiseQuotient (F := F) hD hA hR x y → Prop :=
  relOfConoid (pairwiseQuotientCone (F := F) hD hA hR x y)

lemma pairwiseQuotientCone_add_closed
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    AdditivelyClosed (pairwiseQuotientCone (F := F) hD hA hR x y) := by
  intro a b ha hb
  rcases ha with ⟨za, hza, rfl⟩
  rcases hb with ⟨zb, hzb, rfl⟩
  refine ⟨za + zb, ?_, ?_⟩
  · exact (pairwiseDifferenceCone_add_closed (F := F) hR x y) hza hzb
  · simp

lemma pairwiseQuotientCone_zero_mem
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    (0 : PairwiseQuotient (F := F) hD hA hR x y) ∈
      pairwiseQuotientCone (F := F) hD hA hR x y := by
  refine ⟨0, pairwiseDifferenceCone_zero_mem (F := F) hD hA x y, by simp⟩

lemma pairwiseQuotientCone_pointed
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    ∀ ⦃q : PairwiseQuotient (F := F) hD hA hR x y⦄,
      q ∈ pairwiseQuotientCone (F := F) hD hA hR x y →
      -q ∈ pairwiseQuotientCone (F := F) hD hA hR x y →
      q = 0 := by
  intro q hq hnegq
  rcases hq with ⟨z, hzP, hzEq⟩
  rcases hnegq with ⟨w, hwP, hwEq⟩
  have hsumEq :
      (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (z + w) :
            PairwiseQuotient (F := F) hD hA hR x y) = 0 := by
    calc
      (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (z + w) :
            PairwiseQuotient (F := F) hD hA hR x y)
          = QuotientAddGroup.mk'
              (pairwiseKernelSubgroup (F := F) hD hA hR x y) z
            + QuotientAddGroup.mk'
              (pairwiseKernelSubgroup (F := F) hD hA hR x y) w := by
                simp
      _ = q + (-q) := by simp [hzEq, hwEq]
      _ = 0 := by simp
  have hsumKernel :
      z + w ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := by
    exact (QuotientAddGroup.eq_zero_iff
      (N := pairwiseKernelSubgroup (F := F) hD hA hR x y)
      (x := z + w)).1 hsumEq
  have hnegz : -z ∈ pairwiseDifferenceCone F x y := by
    have haux :
        w + (-(z + w)) ∈ pairwiseDifferenceCone F x y :=
      (pairwiseDifferenceCone_add_closed (F := F) hR x y) hwP hsumKernel.2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using haux
  have hzKernel : z ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := ⟨hzP, hnegz⟩
  have hzZero :
      (QuotientAddGroup.mk'
        (pairwiseKernelSubgroup (F := F) hD hA hR x y) z :
          PairwiseQuotient (F := F) hD hA hR x y) = 0 :=
    (QuotientAddGroup.eq_zero_iff
      (N := pairwiseKernelSubgroup (F := F) hD hA hR x y) (x := z)).2 hzKernel
  exact hzEq.symm.trans hzZero

lemma pairwiseQuotientCone_isPartialOrderConoid
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    IsPartialOrderConoid (pairwiseQuotientCone (F := F) hD hA hR x y) := by
  refine ⟨?_, ?_⟩
  · refine ⟨pairwiseQuotientCone_add_closed (F := F) hD hA hR x y, ?_⟩
    exact pairwiseQuotientCone_zero_mem (F := F) hD hA hR x y
  · intro q hq hnegq
    exact pairwiseQuotientCone_pointed (F := F) hD hA hR x y hq hnegq

lemma pairwiseQuotientRel_homogeneous
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    Homogeneous (pairwiseQuotientRel (F := F) hD hA hR x y) :=
  relOfConoid_homogeneous _

lemma pairwiseQuotientRel_isPartialOrderRel
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    IsPartialOrderRel (pairwiseQuotientRel (F := F) hD hA hR x y) := by
  have hCone :
      IsPartialOrderConoid
        (positiveConoid (pairwiseQuotientRel (F := F) hD hA hR x y)) := by
    simpa [pairwiseQuotientRel, positiveConoid_relOfConoid] using
      (pairwiseQuotientCone_isPartialOrderConoid (F := F) hD hA hR x y)
  exact (lemmaB1a_partial
    (r := pairwiseQuotientRel (F := F) hD hA hR x y)
    (pairwiseQuotientRel_homogeneous (F := F) hD hA hR x y)).2 hCone

noncomputable def pairwiseQuotientPartialOrder
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) where
  le := pairwiseQuotientRel (F := F) hD hA hR x y
  le_refl := (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR x y).1.1
  le_trans := (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR x y).1.2
  le_antisymm := (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR x y).2.antisymm

abbrev PairwiseLinearQuotient
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :=
  LinearExtension (PairwiseQuotient (F := F) hD hA hR x y)

noncomputable def pairwiseLinearMap
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X) :
    ZProfile V →+ PairwiseLinearQuotient (F := F) hD hA hR x y := by
  letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
    pairwiseQuotientPartialOrder (F := F) hD hA hR x y
  refine
    { toFun := fun z =>
        toLinearExtension (α := PairwiseQuotient (F := F) hD hA hR x y)
          ((QuotientAddGroup.mk' (pairwiseKernelSubgroup (F := F) hD hA hR x y) z))
      map_zero' := rfl
      map_add' := by intro a b; rfl }

variable {V X : Type*} {D : Domain V}

lemma pairwiseLinearMap_nonneg_of_winner
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V}
    (hxd : d ∈ winnerCone F x) :
    letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
      pairwiseQuotientPartialOrder (F := F) hD hA hR x y
    (0 : PairwiseLinearQuotient (F := F) hD hA hR x y) ≤
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
  letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
    pairwiseQuotientPartialOrder (F := F) hD hA hR x y
  have hq :
      (0 : PairwiseQuotient (F := F) hD hA hR x y) ≤
        QuotientAddGroup.mk' (pairwiseKernelSubgroup (F := F) hD hA hR x y)
          (toZProfile d) := by
    change
      (QuotientAddGroup.mk' (pairwiseKernelSubgroup (F := F) hD hA hR x y)
          (toZProfile d)
        - 0)
        ∈ pairwiseQuotientCone (F := F) hD hA hR x y
    refine ⟨toZProfile d,
      toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA hxd, ?_⟩
    simp
  simpa [pairwiseLinearMap] using
    (toLinearExtension
      (α := PairwiseQuotient (F := F) hD hA hR x y)).monotone hq

lemma pairwiseQuotientMap_ne_zero_of_winner_loser
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V} {hd : d ∈ D}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    (QuotientAddGroup.mk'
      (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
        PairwiseQuotient (F := F) hD hA hR x y) ≠ 0 := by
  intro hqZero
  have hker :
      toZProfile d ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := by
    exact (QuotientAddGroup.eq_zero_iff
      (N := pairwiseKernelSubgroup (F := F) hD hA hR x y)
      (x := toZProfile d)).1 hqZero
  have hsymm :
      symmPart (pairwiseRel F x y) (toZProfile d) 0 :=
    (mem_pairwiseKernelSubgroup_iff (F := F) hD hA hR
      (x := x) (y := y) (z := toZProfile d)).1 hker
  exact (not_pairwiseRel_toZProfile_zero_of_winner_loser (F := F) hR hxd hynotd) hsymm.1

lemma pairwiseQuotientMap_ne_zero_of_not_pairwiseRel_zero
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V}
    (hnot : ¬ pairwiseRel F x y 0 (toZProfile d)) :
    (QuotientAddGroup.mk'
      (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
        PairwiseQuotient (F := F) hD hA hR x y) ≠ 0 := by
  intro hqZero
  have hker :
      toZProfile d ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := by
    exact (QuotientAddGroup.eq_zero_iff
      (N := pairwiseKernelSubgroup (F := F) hD hA hR x y)
      (x := toZProfile d)).1 hqZero
  have hsymm :
      symmPart (pairwiseRel F x y) (toZProfile d) 0 :=
    (mem_pairwiseKernelSubgroup_iff (F := F) hD hA hR
      (x := x) (y := y) (z := toZProfile d)).1 hker
  exact hnot hsymm.2

lemma pairwiseLinearMap_nonpos_of_winner_swapped
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V}
    (hyd : d ∈ winnerCone F y) :
    letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
      pairwiseQuotientPartialOrder (F := F) hD hA hR x y
    pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) ≤
      (0 : PairwiseLinearQuotient (F := F) hD hA hR x y) := by
  letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
    pairwiseQuotientPartialOrder (F := F) hD hA hR x y
  have hq :
      QuotientAddGroup.mk' (pairwiseKernelSubgroup (F := F) hD hA hR x y)
        (toZProfile d)
        ≤ (0 : PairwiseQuotient (F := F) hD hA hR x y) := by
    change
      (0 -
        QuotientAddGroup.mk' (pairwiseKernelSubgroup (F := F) hD hA hR x y)
          (toZProfile d))
        ∈ pairwiseQuotientCone (F := F) hD hA hR x y
    have hmem :
        -toZProfile d ∈ pairwiseDifferenceCone F x y := by
      simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using
        (pairwiseRel_toZProfile_zero_of_winner_swapped (F := F) hD hA
          (x := x) (y := y) (d := d) hyd)
    refine ⟨-toZProfile d, hmem, ?_⟩
    simp
  simpa [pairwiseLinearMap] using
    (toLinearExtension
      (α := PairwiseQuotient (F := F) hD hA hR x y)).monotone hq

lemma pairwiseLinearMap_not_nonneg_of_winner_loser_swapped
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V} {hd : d ∈ D}
    (hyd : y ∈ F ⟨d, hd⟩)
    (hxnotd : x ∉ F ⟨d, hd⟩) :
    letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
      pairwiseQuotientPartialOrder (F := F) hD hA hR x y
    ¬ (0 : PairwiseLinearQuotient (F := F) hD hA hR x y) ≤
        pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
  letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
    pairwiseQuotientPartialOrder (F := F) hD hA hR x y
  have hnonpos :
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) ≤
        (0 : PairwiseLinearQuotient (F := F) hD hA hR x y) :=
    pairwiseLinearMap_nonpos_of_winner_swapped (F := F) hD hA hR
      (x := x) (y := y) (d := d) (wins_mk (d := d) (hd := hd) hyd)
  have hneq :
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) ≠ 0 := by
    intro hEq
    have hEqQ :
        (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
            PairwiseQuotient (F := F) hD hA hR x y) = 0 := by
      simpa only [pairwiseLinearMap, toLinearExtension] using hEq
    exact
      (pairwiseQuotientMap_ne_zero_of_not_pairwiseRel_zero (F := F) hD hA hR
        (x := x) (y := y) (d := d)
        (not_pairwiseRel_zero_toZProfile_of_winner_loser_swapped (F := F) hR
          (x := x) (y := y) (d := d) (hd := hd) hyd hxnotd))
      hEqQ
  intro hnonneg
  have hzero : (0 : PairwiseLinearQuotient (F := F) hD hA hR x y) =
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) :=
    le_antisymm hnonneg hnonpos
  exact hneq hzero.symm

lemma pairwiseLinearMap_pos_of_winner_loser
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F)
    {x y : X} {d : NProfile V} {hd : d ∈ D}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
      pairwiseQuotientPartialOrder (F := F) hD hA hR x y
    0 < pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
  letI : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
    pairwiseQuotientPartialOrder (F := F) hD hA hR x y
  have hnonneg :
      (0 : PairwiseLinearQuotient (F := F) hD hA hR x y) ≤
        pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) :=
    pairwiseLinearMap_nonneg_of_winner (F := F) hD hA hR
      (x := x) (y := y) (d := d) (wins_mk (d := d) (hd := hd) hxd)
  have hneq :
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) ≠ 0 := by
    intro hEq
    have hEqQ :
        (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
            PairwiseQuotient (F := F) hD hA hR x y) = 0 := by
      simpa only [pairwiseLinearMap, toLinearExtension] using hEq
    have hker :
        toZProfile d ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y :=
      (QuotientAddGroup.eq_zero_iff
        (N := pairwiseKernelSubgroup (F := F) hD hA hR x y)
        (x := toZProfile d)).1 hEqQ
    have hsymm :
        symmPart (pairwiseRel F x y) (toZProfile d) 0 :=
      (mem_pairwiseKernelSubgroup_iff (F := F) hD hA hR
        (x := x) (y := y) (z := toZProfile d)).1 hker
    exact (not_pairwiseRel_toZProfile_zero_of_winner_loser (F := F) hR hxd hynotd) hsymm.1
  refine lt_of_le_of_ne hnonneg ?_
  intro hEq
  exact hneq hEq.symm

/-- If the pairwise kernel subgroup is divisible (in the Appendix-B sense),
the corresponding pairwise quotient is torsion-free. -/
theorem pairwiseQuotient_isAddTorsionFree_of_divisibleKernel
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X)
    (hDiv :
      IsDivisibleSubgroup
        (pairwiseKernelSubgroup (F := F) hD hA hR x y)) :
    IsAddTorsionFree (PairwiseQuotient (F := F) hD hA hR x y) := by
  simpa [PairwiseQuotient] using
    quotient_isAddTorsionFree_of_divisibleSubgroup
      (G := ZProfile V)
      (B := pairwiseKernelSubgroup (F := F) hD hA hR x y) hDiv

/-- Alias for the linearized pairwise quotient codomain. -/
theorem pairwiseLinearQuotient_isAddTorsionFree_of_divisibleKernel
    {F : RuleOn D X} (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hR : Reinforcement D F) (x y : X)
    (hDiv :
      IsDivisibleSubgroup
        (pairwiseKernelSubgroup (F := F) hD hA hR x y)) :
    IsAddTorsionFree (PairwiseLinearQuotient (F := F) hD hA hR x y) := by
  simpa [PairwiseLinearQuotient] using
    pairwiseQuotient_isAddTorsionFree_of_divisibleKernel
      (F := F) hD hA hR x y hDiv

end PairwiseCones

end Pivato
