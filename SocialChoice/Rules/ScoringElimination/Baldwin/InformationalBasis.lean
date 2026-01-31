import Mathlib.Tactic
import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Margin
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringRules.Borda.InformationalBasis

namespace SocialChoice

open Finset

lemma scoreCandidate_borda_le_iff_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂]
    [Fintype A] (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (a b : A) :
    scoreCandidate P₁ (fun r => bordaScore (Fintype.card A) r) a ≤
        scoreCandidate P₁ (fun r => bordaScore (Fintype.card A) r) b ↔
      scoreCandidate P₂ (fun r => bordaScore (Fintype.card A) r) a ≤
        scoreCandidate P₂ (fun r => bordaScore (Fintype.card A) r) b := by
  classical
  let score : Nat → Int := fun r => bordaScore (Fintype.card A) r
  set k₁ : Int := (Fintype.card V₁ : Int) * ((Fintype.card A : Int) - 1)
  set k₂ : Int := (Fintype.card V₂ : Int) * ((Fintype.card A : Int) - 1)
  have hxa :
      2 * scoreCandidate P₁ score a - k₁ =
        2 * scoreCandidate P₂ score a - k₂ := by
    calc
      2 * scoreCandidate P₁ score a - k₁ = c2BordaScore P₁ a := by
        symm
        simpa [score, k₁] using (c2BordaScore_eq_affine (P := P₁) (x := a))
      _ = c2BordaScore P₂ a := by
        simpa using (c2BordaScore_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin a)
      _ = 2 * scoreCandidate P₂ score a - k₂ := by
        simpa [score, k₂] using (c2BordaScore_eq_affine (P := P₂) (x := a))
  have hxb :
      2 * scoreCandidate P₁ score b - k₁ =
        2 * scoreCandidate P₂ score b - k₂ := by
    calc
      2 * scoreCandidate P₁ score b - k₁ = c2BordaScore P₁ b := by
        symm
        simpa [score, k₁] using (c2BordaScore_eq_affine (P := P₁) (x := b))
      _ = c2BordaScore P₂ b := by
        simpa using (c2BordaScore_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin b)
      _ = 2 * scoreCandidate P₂ score b - k₂ := by
        simpa [score, k₂] using (c2BordaScore_eq_affine (P := P₂) (x := b))
  constructor
  · intro hle
    have hle' :
        2 * scoreCandidate P₁ score a - k₁ ≤
          2 * scoreCandidate P₁ score b - k₁ := by
      linarith
    have hle'' :
        2 * scoreCandidate P₂ score a - k₂ ≤
          2 * scoreCandidate P₂ score b - k₂ := by
      simpa [hxa, hxb] using hle'
    linarith
  · intro hle
    have hle' :
        2 * scoreCandidate P₂ score a - k₂ ≤
          2 * scoreCandidate P₂ score b - k₂ := by
      linarith
    have hle'' :
        2 * scoreCandidate P₁ score a - k₁ ≤
          2 * scoreCandidate P₁ score b - k₁ := by
      simpa [hxa, hxb] using hle'
    linarith

lemma lowestScoring_borda_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂]
    [Fintype A] [DecidableEq A] (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    lowestScoring P₁ (fun r => bordaScore (Fintype.card A) r) =
      lowestScoring P₂ (fun r => bordaScore (Fintype.card A) r) := by
  classical
  let score : Nat → Int := fun r => bordaScore (Fintype.card A) r
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · ext a
    constructor
    · intro ha
      have ha' :
          ∀ d : A, scoreCandidate P₁ score a ≤ scoreCandidate P₁ score d :=
        (lowestScoring_iff_forall_le (P := P₁) (score := score) hA a).1 ha
      have ha'' :
          ∀ d : A, scoreCandidate P₂ score a ≤ scoreCandidate P₂ score d := by
        intro d
        exact (scoreCandidate_borda_le_iff_of_margins (P₁ := P₁) (P₂ := P₂) hmargin a d).1
          (ha' d)
      exact (lowestScoring_iff_forall_le (P := P₂) (score := score) hA a).2 ha''
    · intro ha
      have ha' :
          ∀ d : A, scoreCandidate P₂ score a ≤ scoreCandidate P₂ score d :=
        (lowestScoring_iff_forall_le (P := P₂) (score := score) hA a).1 ha
      have ha'' :
          ∀ d : A, scoreCandidate P₁ score a ≤ scoreCandidate P₁ score d := by
        intro d
        exact (scoreCandidate_borda_le_iff_of_margins (P₁ := P₁) (P₂ := P₂) hmargin a d).2
          (ha' d)
      exact (lowestScoring_iff_forall_le (P := P₁) (score := score) hA a).2 ha''
  · simp [lowestScoring, hA]

lemma scoringEliminationAux_borda_marginBased
    {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂] :
    ∀ n : Nat, ∀ (A : Type) [Fintype A] [DecidableEq A],
      (hcard : Fintype.card A = n) →
      ∀ (P₁ : Profile V₁ A) (P₂ : Profile V₂ A),
        (∀ x y : A, margin P₁ x y = margin P₂ x y) →
        scoringEliminationAux bordaScore A P₁ = scoringEliminationAux bordaScore A P₂ := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih A _ _ hcard P₁ P₂ hmargin
  by_cases hle : n ≤ 1
  · have hleA : Fintype.card A ≤ 1 := by simpa [hcard] using hle
    simp [scoringEliminationAux, hleA]
  · have hleA : ¬ Fintype.card A ≤ 1 := by simpa [hcard] using hle
    have hL :
        lowestScoring P₁ (fun r => bordaScore (Fintype.card A) r) =
          lowestScoring P₂ (fun r => bordaScore (Fintype.card A) r) :=
      lowestScoring_borda_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    have hrec :
        ∀ c : A,
          liftFinset (scoringEliminationAux bordaScore _ (restrictProfile P₁ c)) =
            liftFinset (scoringEliminationAux bordaScore _ (restrictProfile P₂ c)) := by
      intro c
      have hmargin' :
          ∀ x y : {x : A // x ≠ c},
            margin (restrictProfile P₁ c) x y = margin (restrictProfile P₂ c) x y := by
        intro x y
        have h1 := margin_eq_margin_restrictProfile (P := P₁) (c := c) (a := x) (b := y)
        have h2 := margin_eq_margin_restrictProfile (P := P₂) (c := c) (a := x) (b := y)
        calc
          margin (restrictProfile P₁ c) x y = margin P₁ x y := by
            simpa using h1.symm
          _ = margin P₂ x y := hmargin x y
          _ = margin (restrictProfile P₂ c) x y := by
            simpa using h2
      have hlt : Fintype.card {x : A // x ≠ c} < n := by
        have hlt' : Fintype.card {x : A // x ≠ c} < Fintype.card A :=
          card_restrict_lt (A := A) c
        simpa [hcard] using hlt'
      have hrec' :=
        ih (Fintype.card {x : A // x ≠ c}) hlt
          (A := {x : A // x ≠ c}) (P₁ := restrictProfile P₁ c) (P₂ := restrictProfile P₂ c)
          (hcard := rfl) hmargin'
      simpa using congrArg (fun s => liftFinset s) hrec'
    have haux₁ :=
      scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := bordaScore) (P := P₁) (hcard := hleA)
    have haux₂ :=
      scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := bordaScore) (P := P₂) (hcard := hleA)
    ext a
    simp [haux₁, haux₂, hL, hrec]

theorem baldwin_marginBased : MarginBased baldwin := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  have h := scoringEliminationAux_borda_marginBased (V₁ := V₁) (V₂ := V₂) (n := Fintype.card A)
    (A := A) (hcard := rfl) (P₁ := P₁) (P₂ := P₂) hmargin
  simpa [baldwin, scoringEliminationRule] using h

end SocialChoice
