import Mathlib.Tactic
import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Margin
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringRules.Borda.InformationalBasis

namespace SocialChoice

open Finset

lemma scoreCandidate_borda_eq_of_margins {V A : Type} [Fintype V] [Fintype A]
    (P₁ P₂ : Profile V A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (a : A) :
    scoreCandidate P₁ (fun r => bordaScore (Fintype.card A) r) a =
      scoreCandidate P₂ (fun r => bordaScore (Fintype.card A) r) a := by
  classical
  set k : Int := (Fintype.card V : Int) * ((Fintype.card A : Int) - 1)
  have hx :
      c2BordaScore P₁ a =
        2 * scoreCandidate P₁ (fun r => bordaScore (Fintype.card A) r) a - k := by
    simpa [k] using (c2BordaScore_eq_affine (P := P₁) (x := a))
  have hy :
      c2BordaScore P₂ a =
        2 * scoreCandidate P₂ (fun r => bordaScore (Fintype.card A) r) a - k := by
    simpa [k] using (c2BordaScore_eq_affine (P := P₂) (x := a))
  have hc2 : c2BordaScore P₁ a = c2BordaScore P₂ a := by
    simpa using (c2BordaScore_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin a)
  linarith [hx, hy, hc2]

lemma lowestScoring_borda_eq_of_margins {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P₁ P₂ : Profile V A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    lowestScoring P₁ (fun r => bordaScore (Fintype.card A) r) =
      lowestScoring P₂ (fun r => bordaScore (Fintype.card A) r) := by
  classical
  have hscore :
      ∀ a : A, scoreCandidate P₁ (fun r => bordaScore (Fintype.card A) r) a =
        scoreCandidate P₂ (fun r => bordaScore (Fintype.card A) r) a :=
    fun a => scoreCandidate_borda_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin a
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · simp [lowestScoring, hA, hscore]
  · simp [lowestScoring, hA]

lemma scoringEliminationAux_borda_marginBased
    {V : Type} [Fintype V] :
    ∀ n : Nat, ∀ (A : Type) [Fintype A] [DecidableEq A],
      (hcard : Fintype.card A = n) →
      ∀ P₁ P₂ : Profile V A,
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
  intro V A _ _ P₁ P₂ hmargin
  classical
  have h := scoringEliminationAux_borda_marginBased (V := V) (n := Fintype.card A)
    (A := A) (hcard := rfl) (P₁ := P₁) (P₂ := P₂) hmargin
  simpa [baldwin, scoringEliminationRule] using h

end SocialChoice
