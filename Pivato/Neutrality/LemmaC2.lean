import Pivato.Neutrality.Defs

/-!
# Lemma C.2 (transport under coordinate permutations)

This file formalizes the two algebraic identities used repeatedly in
Section 3 / Appendix C:
- evaluation commutes with the signal-permutation action,
- successive weight permutations compose multiplicatively.
-/

namespace Pivato

section LemmaC2

variable {V R : Type*}

/-- Lemma C.2(a): evaluating a permuted weight vector equals evaluating on the
permuted profile. -/
lemma lemmaC2a_evalNat_permuteWeight
    [AddCommMonoid R]
    (b : V → R) (n : NProfile V) (π : Equiv.Perm V) :
    evalNat (permuteWeight π b) n = evalNat b (permuteNProfile π n) := by
  let h : V → ℕ →+ R := fun v =>
    { toFun := fun m => m • b v
      map_zero' := by simp
      map_add' := by
        intro m k
        simp [add_nsmul] }
  have hsum :
      (Finsupp.mapDomain π n).sum (fun v m => h v m) =
        n.sum (fun v m => h (π v) m) := by
    exact (Finsupp.sum_mapDomain_index_addMonoidHom (f := π) (s := n) (h := h))
  calc
    evalNat (permuteWeight π b) n = n.sum (fun v m => h (π v) m) := by
      simp [evalNat, permuteWeight, h]
    _ = (Finsupp.mapDomain π n).sum (fun v m => h v m) := by
      symm
      exact hsum
    _ = evalNat b (permuteNProfile π n) := by
      simp [evalNat, permuteNProfile, h, Finsupp.equivMapDomain_eq_mapDomain]

/-- Lemma C.2(b): repeated coordinate permutations multiply as expected. -/
lemma lemmaC2b_permuteWeight_comp
    (b : V → R) (π φ : Equiv.Perm V) :
    permuteWeight φ (permuteWeight π b) = permuteWeight (π * φ) b := by
  exact (permuteWeight_mul (π := π) (φ := φ) (w := b))

end LemmaC2

end Pivato
