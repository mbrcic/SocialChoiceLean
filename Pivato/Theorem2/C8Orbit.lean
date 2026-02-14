import Pivato.Theorem2.C6_C7
import Pivato.Neutrality.Main

/-!
# Stage F skeleton: Lemma C.8 orbit argument

This file tracks the main Appendix C.8 bridge from neutral perfect balance
representations to neutral scoring representations.
-/

namespace Pivato

section C8Orbit

universe uV uX

variable {G : Type*} [Group G]
variable {V : Type uV} {X : Type uX} {R : Type*}
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Fixed-codomain neutral scoring representability predicate used in C.8. -/
def HasNeutralScoringSystem
    [AddCommMonoid R] [Preorder R]
    {D : Domain V} (F : RuleOn D X) : Prop :=
  ∃ S : ScoreSystem R X V, ScoreNeutral mu nu S ∧ F = scoringRule (D := D) S

/-- Lemma C.8 (balance-rule form):
on a cone domain, a neutral perfect balance rule admits a neutral scoring
representation (same codomain type `R`). -/
theorem lemmaC8_of_neutral_perfect_balance
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hNeutral : RuleNeutral mu nu D (balanceRule (D := D) B)) :
    HasNeutralScoringSystem (R := R) (mu := mu) (nu := nu) (D := D)
      (F := balanceRule (D := D) B) := by
  sorry

/-- Lemma C.8 (represented-rule form):
if `F` has a neutral perfect balance representation on a cone domain, then `F`
has a neutral scoring representation. -/
theorem lemmaC8_of_representation
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {F : RuleOn D X}
    (hCone : IsCone D)
    (hRep :
      ∃ B : BalanceSystem R X V,
        BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
          F = balanceRule (D := D) B)
    (hNeutral : RuleNeutral mu nu D F) :
    HasNeutralScoringSystem (R := R) (mu := mu) (nu := nu) (D := D) (F := F) := by
  sorry

end C8Orbit

end Pivato
