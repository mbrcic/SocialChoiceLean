import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

lemma c2BordaScore_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    ∀ x : A, c2BordaScore P₁ x = c2BordaScore P₂ x := by
  intro x
  classical
  simp [c2BordaScore, hmargin]

theorem c2BordaRule_marginBased : MarginBased c2BordaRule := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  have hscore : ∀ x : A, c2BordaScore P₁ x = c2BordaScore P₂ x :=
    c2BordaScore_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
  ext c
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have himage :
        (Finset.univ.image (fun c => c2BordaScore P₁ c)) =
          (Finset.univ.image (fun c => c2BordaScore P₂ c)) := by
        ext x
        simp [hscore]
    simp [c2BordaRule, hA, hscore]
  · simp [c2BordaRule, hA]

theorem borda_marginBased : MarginBased borda := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  have h₁ : borda P₁ = c2BordaRule P₁ := borda_eq_c2BordaRule (P := P₁)
  have h₂ : borda P₂ = c2BordaRule P₂ := borda_eq_c2BordaRule (P := P₂)
  have h :=
    c2BordaRule_marginBased (P₁ := P₁) (P₂ := P₂) hmargin
  simpa [h₁, h₂] using h

end SocialChoice
