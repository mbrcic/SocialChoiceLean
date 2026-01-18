import SocialChoice.Profile

namespace SocialChoice

def reverse_ballot {A : Type} (r : LinearOrder A) : LinearOrder A :=
  LinearOrder.swap A r

def reverse_profile {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) : Profile V A :=
  { pref := fun v => reverse_ballot (P.pref v) }

@[simp] lemma prefers_reverse_profile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (a b : A) :
    Prefers (reverse_profile P) v a b ↔ Prefers P v b a := by
  rfl

def SingletonReversalSymmetry (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (x : A),
    (∃ y, x ≠ y) → f P = {x} → x ∉ f (reverse_profile P)

def ReversalSymmetry (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A),
    f P ≠ Finset.univ → f P ∩ f (reverse_profile P) = ∅

end SocialChoice
