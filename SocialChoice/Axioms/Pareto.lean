import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[scAxiom]
def ParetoEfficiency (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty V] (P : Profile V A) (c d : A),
    (∀ v : V, Prefers P v c d) → d ∉ f P

theorem paretoEfficiency_preservedUnderRefinement :
    PreservedUnderRefinement ParetoEfficiency := by
  intro f g _ _ hfg hZg V A _ _ _ P c d hpref hd
  exact (hZg P c d hpref) (hfg P hd)

end SocialChoice
