import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

lemma maxLoss_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    ∀ a : A, maxLoss P₁ a = maxLoss P₂ a := by
  intro a
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have himage :
        (Finset.univ.image (fun b => margin P₁ b a)) =
          (Finset.univ.image (fun b => margin P₂ b a)) := by
        ext x
        simp [hmargin]
    simp [maxLoss, hA, himage]
  · simp [maxLoss, hA]

lemma minimaxScore_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    minimaxScore P₁ = minimaxScore P₂ := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have hmaxLoss : ∀ a : A, maxLoss P₁ a = maxLoss P₂ a :=
      maxLoss_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    have himage :
        (Finset.univ.image (fun a => maxLoss P₁ a)) =
          (Finset.univ.image (fun a => maxLoss P₂ a)) := by
        ext x
        simp [hmaxLoss]
    simp [minimaxScore, hA, hmaxLoss]
  · simp [minimaxScore, hA]

theorem minimax_marginBased : MarginBased minimax := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  by_cases hA : Nonempty A
  · have hmaxLoss : ∀ a : A, maxLoss P₁ a = maxLoss P₂ a :=
      maxLoss_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    have hscore : minimaxScore P₁ = minimaxScore P₂ :=
      minimaxScore_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    ext a
    simp [minimax, hA, hmaxLoss, hscore]
  · simp [minimax, hA]

end SocialChoice
