import Pivato.Theorem2.C8Claim5

/-!
# Lemma C.8 transport helper

This file discharges the C.8.5 transport hypothesis in the paper's full
permutation-action setting (`G = Perm X`, `mu = id`).
-/

namespace Pivato

section C8Transport

universe uX

variable {X : Type uX}

/-- In the full permutation action on alternatives, any distinct triple can be
transported to any other distinct triple. -/
theorem tripleTransportTo_id_perm
    {x y z : X} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    TripleTransportTo (mu := MonoidHom.id (Equiv.Perm X)) x y z := by
  classical
  intro x' y' z' hxy' hyz' hzx'
  let g1 : Equiv.Perm X := Equiv.swap x' x
  let y1 : X := g1 y'
  have hg1_x' : g1 x' = x := by
    simp [g1]
  have hy1_ne_x : y1 ≠ x := by
    intro hy1x
    have hEq : y' = x' := by
      apply (Equiv.injective g1)
      simpa [y1, hg1_x'] using hy1x
    exact hxy' hEq.symm
  let g2 : Equiv.Perm X := if hy1 : y1 = y then 1 else Equiv.swap y1 y
  have hg2_x : g2 x = x := by
    by_cases hy1 : y1 = y
    · simp [g2, hy1]
    · have hx_ne_y1 : x ≠ y1 := hy1_ne_x.symm
      have hx_ne_y : x ≠ y := hxy
      simp [g2, hy1, Equiv.swap_apply_of_ne_of_ne hx_ne_y1 hx_ne_y]
  have hg2_y1 : g2 y1 = y := by
    by_cases hy1 : y1 = y
    · simp [g2, hy1]
    · simp [g2, hy1, Equiv.swap_apply_left]
  let z1 : X := g1 z'
  have hz1_ne_x : z1 ≠ x := by
    intro hz1x
    have hEq : z' = x' := by
      apply (Equiv.injective g1)
      simpa [z1, hg1_x'] using hz1x
    exact hzx' hEq
  have hz1_ne_y1 : z1 ≠ y1 := by
    intro hz1y1
    have hEq : z' = y' := by
      apply (Equiv.injective g1)
      simpa [z1, y1] using hz1y1
    exact hyz' hEq.symm
  let z2 : X := g2 z1
  have hz2_ne_x : z2 ≠ x := by
    intro hz2x
    have hz1x : z1 = x := by
      apply (Equiv.injective g2)
      simpa [z2, hg2_x] using hz2x
    exact hz1_ne_x hz1x
  have hz2_ne_y : z2 ≠ y := by
    intro hz2y
    have hz1y1 : z1 = y1 := by
      apply (Equiv.injective g2)
      simpa [z2, hg2_y1] using hz2y
    exact hz1_ne_y1 hz1y1
  let g3 : Equiv.Perm X := if hz2 : z2 = z then 1 else Equiv.swap z2 z
  have hg3_x : g3 x = x := by
    by_cases hz2 : z2 = z
    · simp [g3, hz2]
    · have hx_ne_z2 : x ≠ z2 := hz2_ne_x.symm
      have hx_ne_z : x ≠ z := hzx.symm
      simp [g3, hz2, Equiv.swap_apply_of_ne_of_ne hx_ne_z2 hx_ne_z]
  have hg3_y : g3 y = y := by
    by_cases hz2 : z2 = z
    · simp [g3, hz2]
    · have hy_ne_z2 : y ≠ z2 := hz2_ne_y.symm
      have hy_ne_z : y ≠ z := hyz
      simp [g3, hz2, Equiv.swap_apply_of_ne_of_ne hy_ne_z2 hy_ne_z]
  have hg3_z2 : g3 z2 = z := by
    by_cases hz2 : z2 = z
    · simp [g3, hz2]
    · simp [g3, hz2, Equiv.swap_apply_left]
  refine ⟨g3 * g2 * g1, ?_, ?_, ?_⟩
  · calc
      (g3 * g2 * g1) x' = g3 (g2 (g1 x')) := by simp [mul_assoc]
      _ = g3 (g2 x) := by simp [hg1_x']
      _ = g3 x := by simp [hg2_x]
      _ = x := hg3_x
  · calc
      (g3 * g2 * g1) y' = g3 (g2 (g1 y')) := by simp [mul_assoc]
      _ = g3 (g2 y1) := by simp [y1]
      _ = g3 y := by simp [hg2_y1]
      _ = y := hg3_y
  · calc
      (g3 * g2 * g1) z' = g3 (g2 (g1 z')) := by simp [mul_assoc]
      _ = g3 (g2 z1) := by simp [z1]
      _ = g3 z2 := by simp [z2]
      _ = z := hg3_z2

end C8Transport

end Pivato
