import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def Anonymity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (σ : Equiv.Perm V),
    f (permuteVoters P σ) = f P

end SocialChoice
