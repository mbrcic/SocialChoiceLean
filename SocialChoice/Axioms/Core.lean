import SocialChoice.Profile

namespace SocialChoice

def Resolute (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A), (f P).card = 1

def NonTrivial (f : VotingRule) : Prop :=
  ∃ (V A : Type) (instV : Fintype V) (instA : Fintype A),
    let _ := instV
    let _ := instA
    ∃ (P : Profile V A) (c : A), c ∉ f P

def Onto (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (c : A), ∃ P : Profile V A, f P = {c}

end SocialChoice
