import Pivato.Theorem2.C8Orbit
import Pivato.Theorem1.Main

/-!
# Theorem 2 assembly

This file assembles the Stage-F pipeline into directional wrappers and a final
Theorem-2 statement in the generalized-neutrality interface.
-/

namespace Pivato

universe uV uX

section Theorem2

variable {G : Type*} [Group G]
variable {V : Type uV} {X : Type uX}
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
variable {D : Domain V} (F : RuleOn D X)

/-- Theorem-2 target predicate: `F` is representable by some linearly ordered
additive codomain with a `mu`/`nu`-neutral score system. -/
def IsNeutralScoringRepresentable : Prop :=
  ∃ (R : Type (max uV uX)),
    ∃ (instAdd : AddCommGroup R),
    ∃ (instLin : LinearOrder R),
    ∃ (instOrdCancel : IsOrderedCancelAddMonoid R),
    ∃ S : ScoreSystem R X V,
      letI : AddCommGroup R := instAdd
      letI : LinearOrder R := instLin
      letI : IsOrderedCancelAddMonoid R := instOrdCancel
      ScoreNeutral mu nu S ∧ F = scoringRule (D := D) S

private theorem scoringRule_reinforcement_of_isCone
    [DecidableEq V]
    {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} (hCone : IsCone D) (S : ScoreSystem R X V) :
    Reinforcement D (scoringRule (D := D) S) := by
  refine ⟨?_, ?_⟩
  · intro d e hd he _hinter
    exact hCone.1 hd he
  · intro d e hd he hsum hinter
    apply Set.Subset.antisymm
    · intro x hx
      rcases hinter with ⟨z, hzD, hzE⟩
      constructor
      · intro y
        have hyzD : scoreAt S y d ≤ scoreAt S z d := hzD y
        have hzxSum :
            scoreAt S z (d + e) ≤ scoreAt S x (d + e) := hx z
        have hzxSum' :
            scoreAt S z d + scoreAt S z e ≤
              scoreAt S x d + scoreAt S x e := by
          simpa [scoreAt_add (S := S)] using hzxSum
        have hxeLeZe : scoreAt S x e ≤ scoreAt S z e := hzE x
        have hzdLeXd : scoreAt S z d ≤ scoreAt S x d := by
          have hFirst :
              scoreAt S z d + scoreAt S x e ≤
                scoreAt S z d + scoreAt S z e := by
            simpa [add_assoc, add_left_comm, add_comm] using
              (add_le_add_left hxeLeZe (scoreAt S z d))
          have hAux :
              scoreAt S z d + scoreAt S x e ≤
                scoreAt S x d + scoreAt S x e := by
            exact
              le_trans
                hFirst
                hzxSum'
          exact (add_le_add_iff_right (scoreAt S x e)).1 hAux
        exact le_trans hyzD hzdLeXd
      · intro y
        have hyzE : scoreAt S y e ≤ scoreAt S z e := hzE y
        have hzxSum :
            scoreAt S z (d + e) ≤ scoreAt S x (d + e) := hx z
        have hzxSum' :
            scoreAt S z d + scoreAt S z e ≤
              scoreAt S x d + scoreAt S x e := by
          simpa [scoreAt_add (S := S)] using hzxSum
        have hxdLeZd : scoreAt S x d ≤ scoreAt S z d := hzD x
        have hzeLeXe : scoreAt S z e ≤ scoreAt S x e := by
          have hFirst :
              scoreAt S x d + scoreAt S z e ≤
                scoreAt S z d + scoreAt S z e := by
            simpa [add_assoc, add_left_comm, add_comm] using
              (add_le_add_right hxdLeZd (scoreAt S z e))
          have hAux :
              scoreAt S x d + scoreAt S z e ≤
                scoreAt S x d + scoreAt S x e := by
            exact
              le_trans
                hFirst
                hzxSum'
          exact (add_le_add_iff_left (scoreAt S x d)).1 hAux
        exact le_trans hyzE hzeLeXe
    · intro x hx y
      have hyd : scoreAt S y d ≤ scoreAt S x d := hx.1 y
      have hye : scoreAt S y e ≤ scoreAt S x e := hx.2 y
      have hsumLe :
          scoreAt S y d + scoreAt S y e ≤
            scoreAt S x d + scoreAt S x e :=
        add_le_add hyd hye
      simpa [scoreAt_add (S := S)] using hsumLe

/-- Theorem 2 forward direction:
neutrality + reinforcement imply neutral scoring representability on cone
domains (with explicit assumptions for C.1 and C.8 bridge inputs). -/
theorem theorem2_forward
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [Fintype G]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hNE : NonemptyOnDomain D F)
    (hSeed :
      ∀ {R : Type (max uV uX)}
        [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R],
        ∀ B : BalanceSystem R X V,
          BalanceNeutral mu nu B →
          BalanceSkew (B := B) →
          PerfectOn (D := D) (B := B) →
          ∃ x y z : X,
            x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
              BalanceCocycleAtTriple D B x y z)
    (hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := mu) x y z)
    (hNeutral : RuleNeutral mu nu D F)
    (hR : Reinforcement D F) :
    IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F) := by
  rcases lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable
      (F := F) hD hA hR hNE with
      ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hSkew, hPerfect, hFB⟩
  letI : AddCommGroup R := instAdd
  letI : LinearOrder R := instLin
  letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
  letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
  let instOrdCancel : IsOrderedCancelAddMonoid R :=
    IsOrderedCancelAddMonoid.of_add_lt_add_left
      (fun a b c hbc => by
        simpa [add_assoc, add_left_comm, add_comm] using add_lt_add_left hbc a)
  letI : IsOrderedCancelAddMonoid R := instOrdCancel
  have hRep :
      ∃ B0 : BalanceSystem R X V,
        BalanceSkew (B := B0) ∧
          PerfectOn (D := D) (B := B0) ∧
          F = balanceRule (D := D) B0 :=
    ⟨B, hSkew, hPerfect, hFB⟩
  rcases exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty
      (mu := mu) (nu := nu) (D := D) (F := F) hNeutral hRep hNE with
      ⟨Bbar, hNeutralBar, hSkewBar, hPerfectBar, hFBbar⟩
  have hRepBar :
      ∃ B0 : BalanceSystem R X V,
        BalanceSkew (B := B0) ∧
          PerfectOn (D := D) (B := B0) ∧
          F = balanceRule (D := D) B0 :=
    ⟨Bbar, hSkewBar, hPerfectBar, hFBbar⟩
  have hSeedR :
      ∀ B0 : BalanceSystem R X V,
        BalanceNeutral mu nu B0 →
        BalanceSkew (B := B0) →
        PerfectOn (D := D) (B := B0) →
        ∃ x y z : X,
          x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
            BalanceCocycleAtTriple D B0 x y z := by
    intro B0 hNeutral0 hSkew0 hPerfect0
    exact hSeed (R := R) B0 hNeutral0 hSkew0 hPerfect0
  rcases lemmaC8_of_representation
      (mu := mu) (nu := nu) (R := R) (D := D) (F := F)
      hCone hRepBar hNeutral hNE hSeedR hTransport with
      ⟨S, hSNeutral, hFS⟩
  exact ⟨R, instAdd, instLin, instOrdCancel, S, hSNeutral, hFS⟩

/-- Theorem 2 backward direction:
neutral scoring representability implies neutrality and reinforcement under
domain invariance and cone-domain closure. -/
theorem theorem2_backward
    [Finite X] [Nonempty X] [DecidableEq V]
    (hCone : IsCone D)
    (hInv : DomainInvariant nu D)
    (hScore :
      IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F)) :
    RuleNeutral mu nu D F ∧ Reinforcement D F := by
  rcases hScore with ⟨R, instAdd, instLin, instOrdCancel, S, hSNeutral, hFS⟩
  letI : AddCommGroup R := instAdd
  letI : LinearOrder R := instLin
  letI : IsOrderedCancelAddMonoid R := instOrdCancel
  have hNeutralS : RuleNeutral mu nu D (scoringRule (D := D) S) :=
    scoringRule_ruleNeutral_of_scoreNeutral
      (mu := mu) (nu := nu) (S := S) hInv hSNeutral
  have hRS : Reinforcement D (scoringRule (D := D) S) :=
    scoringRule_reinforcement_of_isCone (X := X) (hCone := hCone) S
  refine ⟨?_, ?_⟩
  · simpa [hFS] using hNeutralS
  · simpa [hFS] using hRS

/-- Theorem 2 (generalized-neutrality form under explicit C.1/C.8 inputs). -/
theorem theorem2
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V] [Fintype G]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hInv : DomainInvariant nu D)
    (hNE : NonemptyOnDomain D F)
    (hSeed :
      ∀ {R : Type (max uV uX)}
        [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R],
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
    (RuleNeutral mu nu D F ∧ Reinforcement D F) ↔
      IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F) := by
  constructor
  · intro h
    exact theorem2_forward (mu := mu) (nu := nu) (F := F)
      hD hCone hA hNE hSeed hTransport h.1 h.2
  · intro hScore
    exact theorem2_backward (mu := mu) (nu := nu) (F := F) hCone hInv hScore

end Theorem2

section Theorem2Paper

variable {V : Type uV} {X : Type uX}
variable (nu : Equiv.Perm X →* Equiv.Perm V)
variable {D : Domain V} (F : RuleOn D X)

private lemma no_three_distinct_of_card_le_two
    [Fintype X]
    (hCard : Fintype.card X ≤ 2) :
    ¬ ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  intro hThree
  have hgt : 2 < Fintype.card X := (Fintype.two_lt_card_iff).2 hThree
  exact not_lt_of_ge hCard hgt

private lemma balanceAt_diag_eq_zero_of_skew
    {R : Type*}
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (a : X) (d : NProfile V) :
    balanceAt B a a d = (0 : R) := by
  let t : R := balanceAt B a a d
  have hsk : t = -t := by
    simpa [t] using (hSkew a a d)
  have hsum : t + t = 0 := by
    calc
      t + t = t + (-t) := by
        nth_rewrite 2 [hsk]
        rfl
      _ = 0 := by simp
  have htwo :
      (2 : ℕ) • t = (2 : ℕ) • (0 : R) := by
    simpa [two_nsmul] using hsum
  have ht0 : t = 0 :=
    (nsmul_right_injective (M := R) (by decide : (2 : ℕ) ≠ 0)) htwo
  simpa [t] using ht0

private lemma balanceCocycleOn_of_skew_card_le_two
    {R : Type*}
    [Fintype X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hCard : Fintype.card X ≤ 2) :
    BalanceCocycleOn D B := by
  have hNoThree : ¬ ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z :=
    no_three_distinct_of_card_le_two (X := X) hCard
  intro d hd x y z
  by_cases hxy : x = y
  · subst y
    simp [balanceAt_diag_eq_zero_of_skew (B := B) hSkew x d]
  · by_cases hyz : y = z
    · subst z
      simp [balanceAt_diag_eq_zero_of_skew (B := B) hSkew y d]
    · by_cases hzx : z = x
      · subst z
        calc
          balanceAt B x y d + balanceAt B y x d
              = balanceAt B x y d + (-balanceAt B x y d) := by
                  simp [hSkew y x d]
          _ = 0 := by simp
          _ = balanceAt B x x d := by
              simp [balanceAt_diag_eq_zero_of_skew (B := B) hSkew x d]
      · exfalso
        apply hNoThree
        refine ⟨x, y, z, hxy, ?_, hyz⟩
        intro hxz
        exact hzx hxz.symm

/-- Paper-facing forward direction without branch packaging in the
small-alternative regime `|X| ≤ 2`. -/
theorem theorem2_forward_paper_card_le_two
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [Fintype X]
    (hCard : Fintype.card X ≤ 2)
    (hD : IsDomain D) (_hCone : IsCone D) (hA : GeneralAbstention D F)
    (hNE : NonemptyOnDomain D F)
    (hNeutral : RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F)
    (hR : Reinforcement D F) :
    IsNeutralScoringRepresentable
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F) := by
  rcases lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable
      (F := F) hD hA hR hNE with
      ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hSkew, hPerfect, hFB⟩
  letI : AddCommGroup R := instAdd
  letI : LinearOrder R := instLin
  letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
  letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
  let instOrdCancel : IsOrderedCancelAddMonoid R :=
    IsOrderedCancelAddMonoid.of_add_lt_add_left
      (fun a b c hbc => by
        simpa [add_assoc, add_left_comm, add_comm] using add_lt_add_left hbc a)
  letI : IsOrderedCancelAddMonoid R := instOrdCancel
  have hRep :
      ∃ B0 : BalanceSystem R X V,
        BalanceSkew (B := B0) ∧
          PerfectOn (D := D) (B := B0) ∧
          F = balanceRule (D := D) B0 :=
    ⟨B, hSkew, hPerfect, hFB⟩
  rcases exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F)
      hNeutral hRep hNE with
      ⟨Bbar, hNeutralBar, hSkewBar, hPerfectBar, hFBbar⟩
  have hCocycle : BalanceCocycleOn D Bbar :=
    balanceCocycleOn_of_skew_card_le_two (X := X) (B := Bbar) hSkewBar hCard
  rcases lemmaC4_backward (D := D) Bbar hCocycle with ⟨S0, hBbarS0⟩
  have hScoreRep :
      ∃ S : ScoreSystem R X V, F = scoringRule (D := D) S := by
    refine ⟨S0, ?_⟩
    calc
      F = balanceRule (D := D) Bbar := hFBbar
      _ = scoringRule (D := D) S0 := hBbarS0
  letI : Fintype (Equiv.Perm X) := inferInstance
  have hInv : DomainInvariant nu D := hNeutral.domainInvariant
  rcases (proposition1_of_scoringRepresentation
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F)
      hInv hScoreRep).1 hNeutral with
      ⟨S, hSNeutral, hFS⟩
  exact ⟨R, instAdd, instLin, instOrdCancel, S, hSNeutral, hFS⟩

/-- Paper-facing Theorem 2 wrapper without branch packaging in the
small-alternative regime `|X| ≤ 2`. -/
theorem theorem2_paper_card_le_two
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [Fintype X]
    (hCard : Fintype.card X ≤ 2)
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hInv : DomainInvariant nu D)
    (hNE : NonemptyOnDomain D F) :
    (RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F ∧ Reinforcement D F) ↔
      IsNeutralScoringRepresentable
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F) := by
  constructor
  · intro h
    exact theorem2_forward_paper_card_le_two (nu := nu) (F := F)
      hCard hD hCone hA hNE h.1 h.2
  · intro hScore
    exact theorem2_backward
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (F := F)
      hCone hInv hScore

/-- Paper-facing forward direction (`mu = id` on `Perm X`):
neutrality + reinforcement imply neutral scoring representability.

Compared to the fully generic theorem, this removes explicit `hSeed` and
`hTransport` assumptions by using the C.8 paper wrapper, which discharges
transport and seed extraction internally from cycle-sum packaging. -/
theorem theorem2_forward_paper
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hNE : NonemptyOnDomain D F)
    (hCycle :
      ∀ {R : Type (max uV uX)}
        [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R],
        ∀ B : BalanceSystem R X V,
          BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B →
          BalanceSkew (B := B) →
          PerfectOn (D := D) (B := B) →
          C8CycleSumHypothesis D B)
    (hNeutral : RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F)
    (hR : Reinforcement D F) :
    IsNeutralScoringRepresentable
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F) := by
  rcases lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable
      (F := F) hD hA hR hNE with
      ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hSkew, hPerfect, hFB⟩
  letI : AddCommGroup R := instAdd
  letI : LinearOrder R := instLin
  letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
  letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
  let instOrdCancel : IsOrderedCancelAddMonoid R :=
    IsOrderedCancelAddMonoid.of_add_lt_add_left
      (fun a b c hbc => by
        simpa [add_assoc, add_left_comm, add_comm] using add_lt_add_left hbc a)
  letI : IsOrderedCancelAddMonoid R := instOrdCancel
  have hRep :
      ∃ B0 : BalanceSystem R X V,
        BalanceSkew (B := B0) ∧
          PerfectOn (D := D) (B := B0) ∧
          F = balanceRule (D := D) B0 :=
    ⟨B, hSkew, hPerfect, hFB⟩
  rcases lemmaC8_of_representation_paper
      (nu := nu) (R := R) (D := D) (F := F)
      hCone hRep hNeutral hNE
      (by
        intro B0 hNeutral0 hSkew0 hPerfect0
        exact hCycle (R := R) B0 hNeutral0 hSkew0 hPerfect0) with
      ⟨S, hSNeutral, hFS⟩
  exact ⟨R, instAdd, instLin, instOrdCancel, S, hSNeutral, hFS⟩

/-- Paper-facing Theorem 2 wrapper (`mu = id` on `Perm X`).

This keeps domain-invariance explicit (via `hInv`) and uses cycle-sum
packaging for C.8 instead of explicit seed/transport assumptions. -/
theorem theorem2_paper
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hInv : DomainInvariant nu D)
    (hNE : NonemptyOnDomain D F)
    (hCycle :
      ∀ {R : Type (max uV uX)}
        [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R],
        ∀ B : BalanceSystem R X V,
          BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B →
          BalanceSkew (B := B) →
          PerfectOn (D := D) (B := B) →
          C8CycleSumHypothesis D B) :
    (RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F ∧ Reinforcement D F) ↔
      IsNeutralScoringRepresentable
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F) := by
  constructor
  · intro h
    exact theorem2_forward_paper (nu := nu) (F := F)
      hD hCone hA hNE hCycle h.1 h.2
  · intro hScore
    exact theorem2_backward
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (F := F)
      hCone hInv hScore

end Theorem2Paper

end Pivato
