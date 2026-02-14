import Pivato.Theorem2.C8Seed
import Pivato.Theorem2.C8Transport
import Pivato.Neutrality.Main
import Mathlib.Data.Fintype.Perm

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
    [Fintype G]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (_hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral mu nu B)
    (hSeed :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z)
    (hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := mu) x y z) :
    HasNeutralScoringSystem (R := R) (mu := mu) (nu := nu) (D := D)
      (F := balanceRule (D := D) B) := by
  have hCocycle :
      BalanceCocycleOn D B :=
    claimC85_globalCocycle_of_seedTriple
      (mu := mu) (nu := nu) (B := B) hInv hSkew hNeutralB hSeed hTransport
  rcases lemmaC4_backward (D := D) B hCocycle with ⟨S, hBS⟩
  have hRuleNeutral :
      RuleNeutral mu nu D (balanceRule (D := D) B) :=
    balanceRule_ruleNeutral_of_balanceNeutral
      (mu := mu) (nu := nu) (D := D) (B := B) hInv hNeutralB
  have hScoringRep :
      ∃ S0 : ScoreSystem R X V,
        balanceRule (D := D) B = scoringRule (D := D) S0 := ⟨S, hBS⟩
  rcases (proposition1_of_scoringRepresentation
      (mu := mu) (nu := nu) (D := D) (F := balanceRule (D := D) B)
      hInv hScoringRep).1 hRuleNeutral with ⟨Sbar, hSbarNeutral, hEq⟩
  exact ⟨Sbar, hSbarNeutral, hEq⟩

/-- Intermediate assembly target for C.8:
derive global cocycle on `B` from the Claim-C.8 pipeline. -/
theorem lemmaC8_cocycle_of_neutral_perfect_balance
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (_hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral mu nu B)
    (hSeed :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z)
    (hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := mu) x y z) :
    BalanceCocycleOn D B := by
  exact claimC85_globalCocycle_of_seedTriple
    (mu := mu) (nu := nu) (B := B) hInv hSkew hNeutralB hSeed hTransport

/-- Lemma C.8 (represented-rule form):
if `F` has a neutral perfect balance representation on a cone domain, then `F`
has a neutral scoring representation. -/
theorem lemmaC8_of_representation
    [Finite X] [Nonempty X]
    [Fintype G]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {F : RuleOn D X}
    (hCone : IsCone D)
    (hRep :
      ∃ B : BalanceSystem R X V,
        BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
          F = balanceRule (D := D) B)
    (hNeutral : RuleNeutral mu nu D F)
    (hNE : NonemptyOnDomain D F)
    (hSeed :
      ∀ B : BalanceSystem R X V,
        BalanceNeutral mu nu B →
        BalanceSkew (B := B) →
        PerfectOn (D := D) (B := B) →
        ∃ x y z : X,
          x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
            BalanceCocycleAtTriple D B x y z)
    (hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := mu) x y z) :
    HasNeutralScoringSystem (R := R) (mu := mu) (nu := nu) (D := D) (F := F) := by
  rcases exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty
      (mu := mu) (nu := nu) (D := D) (F := F) hNeutral hRep hNE with
      ⟨Bbar, hNeutralBar, hSkewBar, hPerfectBar, hFBbar⟩
  have hSeedBar :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D Bbar x y z :=
    hSeed Bbar hNeutralBar hSkewBar hPerfectBar
  rcases lemmaC8_of_neutral_perfect_balance
      (mu := mu) (nu := nu) (D := D) (_hCone := hCone) (B := Bbar)
      (hSkew := hSkewBar) (_hPerfect := hPerfectBar)
      (hInv := hNeutral.domainInvariant) (hNeutralB := hNeutralBar)
      (hSeed := hSeedBar) (hTransport := hTransport) with
      ⟨S, hSNeutral, hEqBar⟩
  refine ⟨S, hSNeutral, ?_⟩
  calc
    F = balanceRule (D := D) Bbar := hFBbar
    _ = scoringRule (D := D) S := hEqBar

end C8Orbit

section C8OrbitPaper

universe uV uX

variable {V : Type uV} {X : Type uX} {R : Type*}
variable (nu : Equiv.Perm X →* Equiv.Perm V)

/-- Paper-facing cocycle wrapper for Lemma C.8 in the full permutation-action
setting (`mu = id`): Claim C.8.5 transport and Eq. (C.21) seed generation are
discharged internally. -/
theorem lemmaC8_cocycle_of_neutral_perfect_balance_paper
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hBranch : C8BranchSplitHypothesis (D := D) (B := B)) :
    BalanceCocycleOn D B := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (Equiv.Perm X) := inferInstance
  have hSeed :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z :=
    seedTriple_of_branchSplit (D := D) (B := B) hSkew hBranch
  have hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := MonoidHom.id (Equiv.Perm X)) x y z := by
    intro x y z hxy hyz hzx
    exact tripleTransportTo_id_perm (x := x) (y := y) (z := z) hxy hyz hzx
  exact lemmaC8_cocycle_of_neutral_perfect_balance
    (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D)
    (_hCone := hCone) (B := B) (hSkew := hSkew) (_hPerfect := hPerfect)
    (hInv := hInv) (hNeutralB := hNeutralB) (hSeed := hSeed)
    (hTransport := hTransport)

/-- Paper-facing scoring wrapper for Lemma C.8 in the full permutation-action
setting (`mu = id`): this removes explicit `hSeed`/`hTransport` arguments by
using the C.8.3/C.8.4 branch split plus full permutation transport. -/
theorem lemmaC8_of_neutral_perfect_balance_paper
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hBranch : C8BranchSplitHypothesis (D := D) (B := B)) :
    HasNeutralScoringSystem
      (R := R)
      (mu := MonoidHom.id (Equiv.Perm X))
      (nu := nu)
      (D := D)
      (F := balanceRule (D := D) B) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (Equiv.Perm X) := inferInstance
  have hSeed :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z :=
    seedTriple_of_branchSplit (D := D) (B := B) hSkew hBranch
  have hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := MonoidHom.id (Equiv.Perm X)) x y z := by
    intro x y z hxy hyz hzx
    exact tripleTransportTo_id_perm (x := x) (y := y) (z := z) hxy hyz hzx
  exact lemmaC8_of_neutral_perfect_balance
    (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D)
    (_hCone := hCone) (B := B) (hSkew := hSkew) (_hPerfect := hPerfect)
    (hInv := hInv) (hNeutralB := hNeutralB) (hSeed := hSeed)
    (hTransport := hTransport)

/-- Paper-facing represented-rule wrapper for Lemma C.8 in the full
permutation-action setting (`mu = id`).

This discharges the C.8.5 transport assumption internally and asks for branch
packaging only in the form needed to produce Eq. (C.21) for neutral perfect
balance representations. -/
theorem lemmaC8_of_representation_paper
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {F : RuleOn D X}
    (hCone : IsCone D)
    (hRep :
      ∃ B : BalanceSystem R X V,
        BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
          F = balanceRule (D := D) B)
    (hNeutral : RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F)
    (hNE : NonemptyOnDomain D F)
    (hBranch :
      ∀ B : BalanceSystem R X V,
        BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B →
        BalanceSkew (B := B) →
        PerfectOn (D := D) (B := B) →
        C8BranchSplitHypothesis (D := D) (B := B)) :
    HasNeutralScoringSystem
      (R := R)
      (mu := MonoidHom.id (Equiv.Perm X))
      (nu := nu)
      (D := D)
      (F := F) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (Equiv.Perm X) := inferInstance
  have hSeed :
      ∀ B : BalanceSystem R X V,
        BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B →
        BalanceSkew (B := B) →
        PerfectOn (D := D) (B := B) →
        ∃ x y z : X,
          x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
            BalanceCocycleAtTriple D B x y z := by
    intro B hNeutralB hSkewB hPerfectB
    exact seedTriple_of_branchSplit (D := D) (B := B) hSkewB
      (hBranch B hNeutralB hSkewB hPerfectB)
  have hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := MonoidHom.id (Equiv.Perm X)) x y z := by
    intro x y z hxy hyz hzx
    exact tripleTransportTo_id_perm (x := x) (y := y) (z := z) hxy hyz hzx
  exact lemmaC8_of_representation
    (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F)
    hCone hRep hNeutral hNE hSeed hTransport

end C8OrbitPaper

end Pivato
