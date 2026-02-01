import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

lemma copelandScore2_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    ∀ a : A, copelandScore2 P₁ a = copelandScore2 P₂ a := by
  intro a
  classical
  refine Finset.sum_congr rfl ?_
  intro b hb
  simp [copelandPairScore2, hmargin]

lemma copelandMaxScore2_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    copelandMaxScore2 P₁ = copelandMaxScore2 P₂ := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have hscore : ∀ a : A, copelandScore2 P₁ a = copelandScore2 P₂ a :=
      copelandScore2_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    have himage :
        (Finset.univ.image (fun a => copelandScore2 P₁ a)) =
          (Finset.univ.image (fun a => copelandScore2 P₂ a)) := by
      ext x
      simp [hscore]
    simp [copelandMaxScore2, hA, hscore]
  · simp [copelandMaxScore2, hA]

theorem copeland_marginBased : MarginBased copeland := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  by_cases hA : Nonempty A
  · have hscore : ∀ a : A, copelandScore2 P₁ a = copelandScore2 P₂ a :=
      copelandScore2_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    have hmax : copelandMaxScore2 P₁ = copelandMaxScore2 P₂ :=
      copelandMaxScore2_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    ext a
    simp [copeland, hA, hscore, hmax]
  · simp [copeland, hA]

end SocialChoice
