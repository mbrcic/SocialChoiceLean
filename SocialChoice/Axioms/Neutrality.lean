import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def Neutrality (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (σ : Equiv.Perm A),
    permuteWinners σ (f P) = f (permuteCandidates P σ)

end SocialChoice
