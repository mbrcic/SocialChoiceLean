import SocialChoice.Profile

namespace SocialChoice

def MajorityCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    StrictMajority (votersTop P c) → f P = {c}

def MajorityLoserCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    StrictMajority (votersBottom P c) → c ∉ f P

end SocialChoice
