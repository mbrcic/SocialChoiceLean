import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def Unanimity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    (∀ v : V, TopRank P v c) → f P = {c}

end SocialChoice
