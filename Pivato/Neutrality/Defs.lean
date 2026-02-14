import Pivato.Balance
import Mathlib.GroupTheory.Perm.Basic

/-!
# Generalized neutrality definitions

This file formalizes Section 3 style neutrality data:
- permutation actions on signal coordinates and alternatives,
- domain invariance under signal permutations,
- equivariance predicates for rules, score systems, and balance systems.
-/

namespace Pivato

section NeutralityDefs

variable {G V X R : Type*} [Group G]

/-- Reindex a signal-weight function by a permutation of signals.
This is the paper's right action notation `bπ`. -/
def permuteWeight (π : Equiv.Perm V) (w : V → R) : V → R :=
  fun v => w (π v)

@[simp] lemma permuteWeight_apply (π : Equiv.Perm V) (w : V → R) (v : V) :
    permuteWeight π w v = w (π v) :=
  rfl

@[simp] lemma permuteWeight_one (w : V → R) :
    permuteWeight (1 : Equiv.Perm V) w = w := by
  funext v
  rfl

@[simp] lemma permuteWeight_mul (π φ : Equiv.Perm V) (w : V → R) :
    permuteWeight φ (permuteWeight π w) = permuteWeight (π * φ) w := by
  funext v
  rfl

/-- Image action of a candidate permutation on winner sets. -/
def permuteSet (π : Equiv.Perm X) (S : Set X) : Set X :=
  π '' S

@[simp] lemma mem_permuteSet_iff (π : Equiv.Perm X) (S : Set X) (x : X) :
    x ∈ permuteSet π S ↔ π.symm x ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa
  · intro hx
    exact ⟨π.symm x, hx, by simp⟩

/-- The domain is invariant under the induced signal-permutation action. -/
def DomainInvariant (nu : G →* Equiv.Perm V) (D : Domain V) : Prop :=
  ∀ g ⦃d : NProfile V⦄, d ∈ D → permuteNProfile (nu g) d ∈ D

/-- Generalized neutrality for rules (equivariance plus domain invariance). -/
structure RuleNeutral (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
    (D : Domain V) (F : RuleOn D X) : Prop where
  domainInvariant : DomainInvariant nu D
  equivariant : ∀ g ⦃d : NProfile V⦄ (hd : d ∈ D),
      F ⟨permuteNProfile (nu g) d, domainInvariant g hd⟩ =
        permuteSet (mu g) (F ⟨d, hd⟩)

/-- Generalized neutrality for score systems. -/
def ScoreNeutral (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
    (S : ScoreSystem R X V) : Prop :=
  ∀ g x, permuteWeight (nu g) (S.score ((mu g) x)) = S.score x

/-- Generalized neutrality for balance systems. -/
def BalanceNeutral (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
    (B : BalanceSystem R X V) : Prop :=
  ∀ g x y, permuteWeight (nu g) (B.bal ((mu g) x) ((mu g) y)) = B.bal x y

end NeutralityDefs

end Pivato
