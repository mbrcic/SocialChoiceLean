import Mathlib.Data.Finset.Basic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Meta

namespace SocialChoice

noncomputable def defensibleSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : Finset A := by
  classical
  exact Finset.univ.filter (fun x => ∀ y, ∃ z, margin P z y ≥ margin P y x)

noncomputable def DefensibleSet : VotingRule := by
  intro V A _ _ P
  classical
  exact defensibleSet P

end SocialChoice
