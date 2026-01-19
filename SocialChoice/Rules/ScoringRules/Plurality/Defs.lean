import SocialChoice.Rules
import SocialChoice.Meta

namespace SocialChoice

def pluralityScore (_m r : Nat) : Int := if r = 0 then 1 else 0

@[scRule]
noncomputable def plurality : VotingRule :=
  fun {V A} _ _ (P : Profile V A) =>
    (Finset.univ.filter (fun c => ∀ d : A, topCount P d ≤ topCount P c))

end SocialChoice
