import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

lemma covers_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (x y : A) :
    covers P₁ x y ↔ covers P₂ x y := by
  classical
  simp [covers, margin_pos, hmargin]

lemma uncovered_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (x : A) :
    uncovered P₁ x ↔ uncovered P₂ x := by
  classical
  simp [uncovered, covers, margin_pos, hmargin]

lemma uncoveredSet_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    uncoveredSet (P := P₁) = uncoveredSet (P := P₂) := by
  classical
  ext x
  simp [uncoveredSet, uncovered, covers, margin_pos, hmargin]

/-- UncoveredSet depends only on margins. -/
theorem UncoveredSet_marginBased : MarginBased UncoveredSet := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  have hset : uncoveredSet (P := P₁) = uncoveredSet (P := P₂) :=
    uncoveredSet_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
  simp [UncoveredSet, hset]

end SocialChoice
