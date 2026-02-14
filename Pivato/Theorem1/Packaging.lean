import Pivato.Theorem1.Representation

/-!
# Theorem 1 packaging layer

This file packages Stage-D representation results into reusable predicates and
wrapper theorems.
-/

namespace Pivato

universe uV uX uR

section Packaging

variable {V : Type uV} {X : Type uX} {D : Domain V} (F : RuleOn D X)

/-- Minimal balance representability via a preorder-valued Stage-D witness. -/
def IsBalanceRepresentable : Prop :=
  ∃ (instPre : Preorder (PairCode X V)),
    ∃ B : BalanceSystem (PairCode X V) X V,
      F =
        @balanceRule V X (PairCode X V)
          (by infer_instance) instPre (by infer_instance) D B

/-- Paper-facing perfect representability: existence of a linearly ordered
codomain with a perfect balance-system witness for `F`. -/
def IsPerfectBalanceRepresentable : Prop :=
  ∃ (R : Type (max uV uX)),
    ∃ (instAdd : AddCommGroup R),
    ∃ (instLin : LinearOrder R),
    ∃ B : BalanceSystem R X V,
      letI : AddCommGroup R := instAdd
      letI : LinearOrder R := instLin
      PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B

/-- Strengthened representability for the corrected converse direction. -/
def IsPerfectSkewBalanceRepresentable [DecidableEq V] : Prop :=
  ∃ (R : Type*),
    ∃ (instAdd : AddCommGroup R),
    ∃ (instLin : LinearOrder R),
    ∃ (instCovLe : CovariantClass R R (fun a b => a + b) (· ≤ ·)),
    ∃ (instCovLt : CovariantClass R R (fun a b => a + b) (· < ·)),
    ∃ B : BalanceSystem R X V,
      letI : AddCommGroup R := instAdd
      letI : LinearOrder R := instLin
      letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
      letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
      BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B

/-- Paper-facing synonym: in the paper, skew-symmetry is part of the
definition of a balance system, so this is the same predicate. -/
def IsPerfectBalanceRuleRepresentable [DecidableEq V] : Prop :=
  ∃ (R : Type uR),
    ∃ (instAdd : AddCommGroup R),
    ∃ (instLin : LinearOrder R),
    ∃ (instCovLe : CovariantClass R R (fun a b => a + b) (· ≤ ·)),
    ∃ (instCovLt : CovariantClass R R (fun a b => a + b) (· < ·)),
    ∃ B : BalanceSystem R X V,
      letI : AddCommGroup R := instAdd
      letI : LinearOrder R := instLin
      letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
      letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
      BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B

/-- Theorem 1 forward packaging: reinforcement gives balance representability. -/
theorem isBalanceRepresentable_of_reinforcement
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    IsBalanceRepresentable (F := F) := by
  let instPre : Preorder (PairCode X V) := winnerConePreorder (F := F) hD hA hR
  have hRep :
      ∃ B : BalanceSystem (PairCode X V) X V,
        F = @balanceRule V X (PairCode X V) (by infer_instance) instPre
          (by infer_instance) D B := by
    simpa [instPre] using
      (reinforcement_has_balance_representation (F := F) hD hA hR)
  rcases hRep with ⟨B, hFB⟩
  exact ⟨instPre, B, hFB⟩

/-- Corrected Theorem 1 converse packaging: a perfect+skew balance representation
implies reinforcement, assuming weak additivity on the represented rule. -/
theorem reinforcement_of_perfectSkewBalanceRepresentation
    [DecidableEq V]
    (hWA : WeaklyAdditive D F)
    (hRep : IsPerfectSkewBalanceRepresentable (F := F)) :
    Reinforcement D F := by
  rcases hRep with ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hRepB⟩
  letI : AddCommGroup R := instAdd
  letI : LinearOrder R := instLin
  letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
  letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
  rcases hRepB with ⟨hskew, hperfect, hFB⟩
  have hWA_B : WeaklyAdditive D (balanceRule (D := D) B) := by
    simpa [hFB] using hWA
  have hR_B : Reinforcement D (balanceRule (D := D) B) :=
    balanceRule_reinforcement_of_perfect (D := D) (B := B) hWA_B hskew hperfect
  simpa [hFB] using hR_B

/-- Paper-facing converse packaging name:
a perfect balance-rule representation (where skew is part of the balance-system
interface) implies reinforcement, assuming weak additivity. -/
theorem reinforcement_of_perfectBalanceRepresentation
    [DecidableEq V]
    (hWA : WeaklyAdditive D F)
    (hRep : IsPerfectBalanceRuleRepresentable (F := F)) :
    Reinforcement D F :=
  reinforcement_of_perfectSkewBalanceRepresentation (F := F) hWA hRep

/-- Corrected Theorem 1 (forward wrapper): reinforcement gives a balance
representation. -/
theorem theorem1_corrected
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) :
    Reinforcement D F → IsBalanceRepresentable (F := F) := by
  intro hR
  exact isBalanceRepresentable_of_reinforcement (F := F) hD hA hR

/-- Corrected Theorem 1 converse wrapper under explicit perfect+skew structure
under the explicit Stage-D predicate. -/
theorem theorem1_corrected_converse
    [DecidableEq V]
    (hWA : WeaklyAdditive D F)
    (hRep : IsPerfectSkewBalanceRepresentable (F := F)) :
    Reinforcement D F :=
  reinforcement_of_perfectSkewBalanceRepresentation (F := F) hWA hRep

/-- Paper-facing converse wrapper using the paper-style predicate name
under the explicit Stage-D predicate. -/
theorem theorem1_corrected_converse_paper
    [DecidableEq V]
    (hWA : WeaklyAdditive D F)
    (hRep : IsPerfectBalanceRuleRepresentable (F := F)) :
    Reinforcement D F :=
  reinforcement_of_perfectBalanceRepresentation (F := F) hWA hRep

end Packaging

end Pivato
