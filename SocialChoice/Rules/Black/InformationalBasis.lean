import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.InformationalBasis

namespace SocialChoice

theorem black_marginBased : MarginBased black := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  have hcw :
      ∀ x : A, CondorcetWinner P₁ x ↔ CondorcetWinner P₂ x := by
    intro x
    constructor
    · intro hx
      apply (CondorcetWinner_iff_margin_pos P₂ x).2
      intro y hy
      have hpos := (CondorcetWinner_iff_margin_pos P₁ x).1 hx y hy
      simpa [margin_pos, hmargin] using hpos
    · intro hx
      apply (CondorcetWinner_iff_margin_pos P₁ x).2
      intro y hy
      have hpos := (CondorcetWinner_iff_margin_pos P₂ x).1 hx y hy
      simpa [margin_pos, hmargin] using hpos
  by_cases h₁ : ∃ x, CondorcetWinner P₁ x
  · have h₂ : ∃ x, CondorcetWinner P₂ x := by
      rcases h₁ with ⟨x, hx⟩
      exact ⟨x, (hcw x).1 hx⟩
    have hchoose₁ : CondorcetWinner P₁ (Classical.choose h₁) := Classical.choose_spec h₁
    have hchoose₂ : CondorcetWinner P₂ (Classical.choose h₂) := Classical.choose_spec h₂
    have hchoose₁' : CondorcetWinner P₂ (Classical.choose h₁) := (hcw _).1 hchoose₁
    have hEq :
        Classical.choose h₂ = Classical.choose h₁ :=
      CondorcetWinner_unique (P := P₂) (hx := hchoose₂) (hy := hchoose₁')
    simp [black, h₁, h₂, hEq]
  · have h₂ : ¬ ∃ x, CondorcetWinner P₂ x := by
      intro h₂
      rcases h₂ with ⟨x, hx⟩
      exact h₁ ⟨x, (hcw x).2 hx⟩
    have hborda : borda P₁ = borda P₂ := borda_marginBased (P₁ := P₁) (P₂ := P₂) hmargin
    simp [black, h₁, h₂, hborda]

end SocialChoice
