import SocialChoice.Profile

namespace SocialChoice

def Anonymity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (σ : Equiv.Perm V),
    f (permuteVoters P σ) = f P

end SocialChoice
