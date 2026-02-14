import Pivato.Rules
import Mathlib.Data.Fintype.Lattice

/-!
# Scoring semantics on count-profile domains
-/

namespace Pivato

section Evaluation

variable {V R : Type*} [AddCommMonoid R]

/-- Evaluate a signal weight function on an anonymous count profile. -/
def evalNat (w : V → R) (d : NProfile V) : R :=
  d.sum (fun v n => n • w v)

@[simp] lemma evalNat_zero (w : V → R) :
    evalNat w (0 : NProfile V) = 0 := by
  simp [evalNat]

lemma evalNat_add {V R : Type*} [AddCommMonoid R] [DecidableEq V]
    (w : V → R) (d e : NProfile V) :
    evalNat w (d + e) = evalNat w d + evalNat w e := by
  unfold evalNat
  simpa [add_nsmul] using
    (Finsupp.sum_add_index (f := d) (g := e)
      (h := fun v n => n • w v)
      (by intro a ha; simp)
      (by intro a ha b₁ b₂; simp [add_nsmul]))

end Evaluation

section Scoring

variable {V X R : Type*}

/-- A score system assigns each alternative a weight function on signals. -/
structure ScoreSystem (R X V : Type*) where
  score : X → V → R

variable [AddCommMonoid R]

/-- Total score assigned to `x` by profile `d`. -/
def scoreAt (S : ScoreSystem R X V) (x : X) (d : NProfile V) : R :=
  evalNat (S.score x) d

variable [Preorder R] {D : Domain V}

/-- The scoring correspondence: alternatives with maximal total score. -/
def scoringRule (S : ScoreSystem R X V) : RuleOn D X :=
  fun d => {x | ∀ y, scoreAt S y d.1 ≤ scoreAt S x d.1}

lemma mem_scoringRule_iff {S : ScoreSystem R X V} {d : {d : NProfile V // d ∈ D}} {x : X} :
    x ∈ scoringRule (D := D) S d ↔ ∀ y, scoreAt S y d.1 ≤ scoreAt S x d.1 :=
  Iff.rfl

omit [Preorder R] in
lemma scoreAt_add [DecidableEq V] (S : ScoreSystem R X V) (x : X)
    (d e : NProfile V) :
    scoreAt S x (d + e) = scoreAt S x d + scoreAt S x e :=
  evalNat_add (w := S.score x) d e

end Scoring

section ScoringNonempty

variable {V X R : Type*}
variable [AddCommMonoid R] [LinearOrder R]
variable {D : Domain V}

lemma scoringRule_nonempty [Finite X] [Nonempty X]
    (S : ScoreSystem R X V) (d : {d : NProfile V // d ∈ D}) :
    (scoringRule (D := D) S d).Nonempty := by
  rcases Finite.exists_max (f := fun x : X => scoreAt S x d.1) with ⟨x, hx⟩
  exact ⟨x, fun y => hx y⟩

lemma scoringRule_nonemptyOnDomain [Finite X] [Nonempty X]
    (S : ScoreSystem R X V) :
    NonemptyOnDomain D (scoringRule (D := D) S) := by
  intro d
  exact scoringRule_nonempty (D := D) S d

end ScoringNonempty

end Pivato
