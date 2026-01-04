import SocialChoice.Profile

namespace SocialChoice

open Finset

def simpleLift {V A : Type} [Fintype V] [Fintype A]
    (P' P : Profile V A) (x : A) : Prop :=
  (∀ v a b, a ≠ x → b ≠ x → (Prefers P v a b ↔ Prefers P' v a b)) ∧
    ∀ a v, (Prefers P v x a → Prefers P' v x a) ∧
      (Prefers P' v a x → Prefers P v a x)

def Monotonicity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P P' : Profile V A) (x : A),
    x ∈ f P → simpleLift P' P x → x ∈ f P'

end SocialChoice
