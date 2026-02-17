import Pivato.Theorem2.C8Bridge
import Pivato.Theorem2.C8Transport
import Pivato.Neutrality.Main
import Mathlib.Data.Fintype.Perm

/-!
# Lemma C.8 orbit argument

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
theorem lemmaC8_cocycle_of_neutral_perfect_balance_paper_of_cycle
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hCycle : C8CycleSumHypothesis (D := D) (B := B)) :
    BalanceCocycleOn D B := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (Equiv.Perm X) := inferInstance
  have hSeed :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z :=
    seedTriple_of_branchSplit (D := D) (B := B) hSkew
      (branchSplit_of_cycleSumHypothesis (D := D) (B := B) hCycle)
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

/-- Paper-facing cocycle wrapper for Lemma C.8 in the full permutation-action
setting (`mu = id`): no explicit C.8 cycle-sum argument is required. -/
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
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B)) :
    BalanceCocycleOn D B := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq V := Classical.decEq V
  letI : Fintype X := Fintype.ofFinite X
  by_cases hCard : Fintype.card X ≤ 2
  · exact balanceCocycleOn_of_skew_card_le_two
      (X := X) (D := D) (B := B) hSkew hCard
  · have hCardGt : 2 < Fintype.card X := Nat.lt_of_not_ge hCard
    have hCycle : C8CycleSumHypothesis (D := D) (B := B) :=
      c8CycleSumHypothesis_of_neutral_perfect_balance_paper
        (nu := nu) (R := R) (D := D)
        hCone B hSkew hPerfect hInv hNeutralB hNE hCardGt
    exact lemmaC8_cocycle_of_neutral_perfect_balance_paper_of_cycle
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hCycle

/-- Paper-facing scoring wrapper for Lemma C.8 in the full permutation-action
setting (`mu = id`): this removes explicit `hSeed`/`hTransport` arguments by
using the C.8.3/C.8.4 branch split plus full permutation transport. -/
theorem lemmaC8_of_neutral_perfect_balance_paper_of_cycle
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hCycle : C8CycleSumHypothesis (D := D) (B := B)) :
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
    seedTriple_of_branchSplit (D := D) (B := B) hSkew
      (branchSplit_of_cycleSumHypothesis (D := D) (B := B) hCycle)
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

/-- Paper-facing scoring wrapper for Lemma C.8 in the full permutation-action
setting (`mu = id`): no explicit C.8 cycle-sum argument is required. -/
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
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B)) :
    HasNeutralScoringSystem
      (R := R)
      (mu := MonoidHom.id (Equiv.Perm X))
      (nu := nu)
      (D := D)
      (F := balanceRule (D := D) B) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  letI : DecidableEq V := Classical.decEq V
  letI : Fintype X := Fintype.ofFinite X
  by_cases hCard : Fintype.card X ≤ 2
  · have hCocycle : BalanceCocycleOn D B :=
      balanceCocycleOn_of_skew_card_le_two
        (X := X) (D := D) (B := B) hSkew hCard
    rcases lemmaC4_backward (D := D) B hCocycle with ⟨S, hBS⟩
    have hRuleNeutral :
        RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D (balanceRule (D := D) B) :=
      balanceRule_ruleNeutral_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (B := B) hInv hNeutralB
    have hScoringRep :
        ∃ S0 : ScoreSystem R X V,
          balanceRule (D := D) B = scoringRule (D := D) S0 := ⟨S, hBS⟩
    rcases (proposition1_of_scoringRepresentation
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D)
        (F := balanceRule (D := D) B)
        hInv hScoringRep).1 hRuleNeutral with ⟨Sbar, hSbarNeutral, hEq⟩
    exact ⟨Sbar, hSbarNeutral, hEq⟩
  · have hCardGt : 2 < Fintype.card X := Nat.lt_of_not_ge hCard
    have hCycle : C8CycleSumHypothesis (D := D) (B := B) :=
      c8CycleSumHypothesis_of_neutral_perfect_balance_paper
        (nu := nu) (R := R) (D := D)
        hCone B hSkew hPerfect hInv hNeutralB hNE hCardGt
    exact lemmaC8_of_neutral_perfect_balance_paper_of_cycle
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hCycle

/-- Three-cycle branch wrapper:
if a three-cycle orbit block (built from period `M + 1`) has divisible hull equal
to the whole-domain hull, then Eq. (C.21) follows and we obtain Lemma C.8. -/
theorem lemmaC8_of_neutral_perfect_balance_threeCycleHullEq
    [Finite X] [Nonempty X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (φ : Equiv.Perm X)
    (M : ℕ)
    (hThreeDiv : 3 ∣ M + 1)
    {x y z : X}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hφx : φ x = z) (hφy : φ y = x) (hφz : φ z = y)
    (K Kblock : AddSubgroup (ZProfile V))
    (hHullD : IsDivisibleHull (domainImageZ D) K)
    (hHullBlock :
      IsDivisibleHull
        (domainImageZ
          (orbitBlockDomain D (balanceRule (D := D) B)
            (orbitProfileSum (nu φ) M)
            (by
              intro d hd
              exact orbitProfileSum_mem_of_domainInvariant
                (D := D) hCone nu hInv φ hd M)
            (orbitSet φ x)))
        Kblock)
    (hHullEq : K = Kblock) :
    HasNeutralScoringSystem
      (R := R)
      (mu := MonoidHom.id (Equiv.Perm X))
      (nu := nu)
      (D := D)
      (F := balanceRule (D := D) B) := by
  have hCycle : C8CycleSumHypothesis (D := D) (B := B) := by
    have horbit : ∀ {d : NProfile V}, d ∈ D → orbitProfileSum (nu φ) M d ∈ D := by
      intro d hd
      exact orbitProfileSum_mem_of_domainInvariant
        (D := D) hCone nu hInv φ hd M
    exact cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq
      (D := D) (B := B) hSkew nu hNeutralB φ M hThreeDiv horbit
      hxy hyz hzx hφx hφy hφz
      K Kblock hHullD hHullBlock hHullEq
  exact lemmaC8_of_neutral_perfect_balance_paper_of_cycle
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hCycle

/-- Paper-facing represented-rule wrapper for Lemma C.8 in the full
permutation-action setting (`mu = id`).

This discharges C.8 transport and cycle packaging assumptions internally. -/
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
    (hNE : NonemptyOnDomain D F) :
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
  rcases exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F)
      hNeutral hRep hNE with
      ⟨Bbar, hNeutralBar, hSkewBar, hPerfectBar, hFBbar⟩
  have hNEBar : NonemptyOnDomain D (balanceRule (D := D) Bbar) := by
    simpa [hFBbar] using hNE
  rcases lemmaC8_of_neutral_perfect_balance_paper
      (nu := nu) (R := R) (D := D)
      hCone Bbar hSkewBar hPerfectBar hNeutral.domainInvariant hNeutralBar hNEBar with
      ⟨S, hSNeutral, hEqBar⟩
  refine ⟨S, hSNeutral, ?_⟩
  calc
    F = balanceRule (D := D) Bbar := hFBbar
    _ = scoringRule (D := D) S := hEqBar

end C8OrbitPaper

end Pivato
