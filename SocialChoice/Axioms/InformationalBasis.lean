import SocialChoice.Margin
import SocialChoice.Meta
import SocialChoice.Rules

namespace SocialChoice

@[scAxiom]
def MarginBased (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P₁ P₂ : Profile V A),
    (∀ x y : A, margin P₁ x y = margin P₂ x y) → f P₁ = f P₂

@[scAxiom]
def TopsOnly (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P₁ P₂ : Profile V A),
    (∀ a : A, topCount P₁ a = topCount P₂ a) → f P₁ = f P₂

end SocialChoice
