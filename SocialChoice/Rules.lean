import SocialChoice.Profile
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset

noncomputable def topCount {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Nat :=
  (votersTop P c).card

-- Concrete rules.
noncomputable def trivialRule : VotingRule :=
  fun {V A} _ _ (_ : Profile V A) => (Finset.univ : Finset A)

end SocialChoice
