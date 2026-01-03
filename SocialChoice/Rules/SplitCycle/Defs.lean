import Mathlib.Data.Finset.Basic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Cycles

namespace SocialChoice

noncomputable def splitCycleDefeats {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) : Prop :=
  margin_pos P x y ∧
    ¬ ∃ c : List A, x ∈ c ∧ y ∈ c ∧
      cycle (fun a b => margin P x y ≤ margin P a b) c

noncomputable def splitCycle : VotingRule := by
  intro V A _ _ P
  classical
  exact Finset.univ.filter (fun x => ∀ y, ¬ splitCycleDefeats P y x)

end SocialChoice
