import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

lemma splitCycleDefeats_eq_of_margins {V A : Type} [Fintype V] [Fintype A]
    (P₁ P₂ : Profile V A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (x y : A) :
    splitCycleDefeats P₁ x y ↔ splitCycleDefeats P₂ x y := by
  simp [splitCycleDefeats, margin_pos, hmargin]

theorem splitCycle_marginBased : MarginBased splitCycle := by
  intro V A _ _ P₁ P₂ hmargin
  classical
  ext x
  simp [splitCycle, splitCycleDefeats_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin]

end SocialChoice
