import SocialChoice.Profile
import SocialChoice.Axioms.Resolute

namespace SocialChoice

/-!
# Core Voting Rule Properties

This file collects basic properties of voting rules.
The `Resolute` definition is in `Axioms/Resolute.lean`.
-/

/-- A voting rule is non-trivial if some candidate can lose. -/
def NonTrivial (f : VotingRule) : Prop :=
  ∃ (V A : Type) (instV : Fintype V) (instA : Fintype A),
    let _ := instV
    let _ := instA
    ∃ (P : Profile V A) (c : A), c ∉ f P

/-- A voting rule is onto if every candidate can win. -/
def Onto (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (c : A), ∃ P : Profile V A, f P = {c}

end SocialChoice
