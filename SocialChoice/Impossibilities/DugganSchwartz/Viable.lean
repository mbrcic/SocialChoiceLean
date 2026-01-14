import SocialChoice.Profile

namespace SocialChoice

/-- Every alternative is viable if it is the unique winner at some profile. -/
def Viable (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A], ∀ a : A, ∃ P : Profile V A, f P = {a}

end SocialChoice
