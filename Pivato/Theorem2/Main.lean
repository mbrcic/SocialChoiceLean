import Pivato.Theorem2.C8Orbit
import Pivato.Theorem1.Main

/-!
# Stage F skeleton: Theorem 2

This file tracks the final theorem statement and two directional wrappers for
Theorem 2. Proofs are intentionally left as `sorry` TODOs.
-/

namespace Pivato

universe uV uX uR

section Theorem2

variable {G : Type*} [Group G]
variable {V : Type uV} {X : Type uX}
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
variable {D : Domain V} (F : RuleOn D X)

/-- Theorem-2 target predicate: `F` is representable by some linearly ordered
additive codomain with a `mu`/`nu`-neutral score system. -/
def IsNeutralScoringRepresentable : Prop :=
  ∃ (R : Type uR),
    ∃ (instAdd : AddCommGroup R),
    ∃ (instLin : LinearOrder R),
    ∃ (instOrdCancel : IsOrderedCancelAddMonoid R),
    ∃ S : ScoreSystem R X V,
      letI : AddCommGroup R := instAdd
      letI : LinearOrder R := instLin
      letI : IsOrderedCancelAddMonoid R := instOrdCancel
      ScoreNeutral mu nu S ∧ F = scoringRule (D := D) S

/-- Theorem 2 forward direction (tracked TODO):
neutrality + reinforcement imply neutral scoring representability on cone
domains (with explicit `IsDomain`/`GeneralAbstention` assumptions). -/
theorem theorem2_forward
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hNeutral : RuleNeutral mu nu D F)
    (hR : Reinforcement D F) :
    IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F) := by
  sorry

/-- Theorem 2 backward direction (tracked TODO):
neutral scoring representability implies neutrality and reinforcement. -/
theorem theorem2_backward
    [Finite X] [Nonempty X]
    (hScore :
      IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F)) :
    RuleNeutral mu nu D F ∧ Reinforcement D F := by
  sorry

/-- Theorem 2 (generalized-neutrality form, tracked TODO). -/
theorem theorem2
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F) :
    (RuleNeutral mu nu D F ∧ Reinforcement D F) ↔
      IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F) := by
  constructor
  · intro h
    exact theorem2_forward (mu := mu) (nu := nu) (F := F) hD hCone hA h.1 h.2
  · intro hScore
    exact theorem2_backward (mu := mu) (nu := nu) (F := F) hScore

end Theorem2

end Pivato

