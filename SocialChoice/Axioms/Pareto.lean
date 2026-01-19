import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def ParetoEfficiency (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty V] (P : Profile V A) (c d : A),
    (∀ v : V, Prefers P v c d) → d ∉ f P

end SocialChoice
