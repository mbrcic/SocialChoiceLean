import SocialChoice.Profile

namespace SocialChoice

def IndependenceOfLosers (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A) (c : A),
    c ∉ f P →
      liftWinners (f (restrictCandidates P (fun a => a ≠ c))) = f P

def IndependenceOfDominated (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A) (c d : A),
    (∀ v : V, Prefers P v c d) →
      liftWinners (f (restrictCandidates P (fun a => a ≠ d))) = f P

def IndependenceOfUniversallyLeastPreferred (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A) (c d : A),
    c ≠ d →
      (∀ v : V, BottomRank P v d) →
        liftWinners (f (restrictCandidates P (fun a => a ≠ d))) = f P

end SocialChoice
