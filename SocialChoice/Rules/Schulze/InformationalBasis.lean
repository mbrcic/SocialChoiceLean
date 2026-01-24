import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.Schulze.Defs

namespace SocialChoice

lemma pathMargins_eq_of_margins {V A : Type} [Fintype V] [Fintype A]
    (P₁ P₂ : Profile V A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    ∀ l : List A, pathMargins P₁ l = pathMargins P₂ l := by
  intro l
  induction l with
  | nil =>
      simp [pathMargins]
  | cons a t ih =>
      cases t with
      | nil =>
          simp [pathMargins]
      | cons b t' =>
          simp [pathMargins, hmargin, ih]

lemma pathStrength_eq_of_margins {V A : Type} [Fintype V] [Fintype A]
    (P₁ P₂ : Profile V A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    ∀ l : List A, pathStrength P₁ l = pathStrength P₂ l := by
  intro l
  have hpm := pathMargins_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin l
  simp [pathStrength_eq_minList, hpm]

lemma strongestPath_eq_of_margins {V A : Type} [Fintype V] [Fintype A]
  (P₁ P₂ : Profile V A)
  (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (a b : A) :
    strongestPath P₁ a b = strongestPath P₂ a b := by
  classical
  by_cases hne : (pathsUpTo (Fintype.card A) a b).Nonempty
  · have hstrengths :
        (pathsUpTo (Fintype.card A) a b).image (fun l => pathStrength P₁ l) =
          (pathsUpTo (Fintype.card A) a b).image (fun l => pathStrength P₂ l) := by
        ext x
        simp [pathStrength_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin]
    simp [strongestPath, hne, pathStrength_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin]
  · simp [strongestPath, hne, hmargin]

lemma schulzeDefeats_eq_of_margins {V A : Type} [Fintype V] [Fintype A]
    (P₁ P₂ : Profile V A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (a b : A) :
    schulzeDefeats P₁ a b ↔ schulzeDefeats P₂ a b := by
  simp [schulzeDefeats, strongestPath_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin]

theorem schulze_marginBased : MarginBased schulze := by
  intro V A _ _ P₁ P₂ hmargin
  classical
  ext a
  simp [schulze, schulzeDefeats_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin]

end SocialChoice
