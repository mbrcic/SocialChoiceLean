import SocialChoice.Profile

namespace SocialChoice

universe u

def Reinforcement (f : VotingRule) : Prop :=
  ∀ {V W A : Type u} [Fintype V] [Fintype W] [Fintype A] [DecidableEq A]
      (P₁ : Profile V A) (P₂ : Profile W A),
    (f P₁ ∩ f P₂).Nonempty →
      f (unionProfiles P₁ P₂) = f P₁ ∩ f P₂

def SubsetReinforcement (f : VotingRule) : Prop :=
  ∀ {V W A : Type u} [Fintype V] [Fintype W] [Fintype A] [DecidableEq A]
      (P₁ : Profile V A) (P₂ : Profile W A),
    f P₁ ∩ f P₂ ⊆ f (unionProfiles P₁ P₂)

lemma reinforcement_subset {f : VotingRule} :
    Reinforcement f → SubsetReinforcement f := by
  intro h V W A _ _ _ _ P₁ P₂ x hx
  have hnonempty : (f P₁ ∩ f P₂).Nonempty := ⟨x, hx⟩
  have hEq := h P₁ P₂ hnonempty
  simpa [hEq] using hx

end SocialChoice
