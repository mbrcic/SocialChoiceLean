import Mathlib.Data.Finset.Basic
import SocialChoice.Profile
import SocialChoice.Margin

namespace SocialChoice

open Finset

section Minimax

variable {V A : Type} [Fintype V] [Fintype A]

noncomputable def maxLoss (P : Profile V A) (a : A) : Int := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let losses := Finset.univ.image (fun b => margin P b a)
    have hLosses : losses.Nonempty := by
      rcases hA with ⟨b, hb⟩
      exact ⟨margin P b a, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    exact Finset.max' losses hLosses
  · exact 0

noncomputable def minimaxScore (P : Profile V A) : Int := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let scores := Finset.univ.image (fun a => maxLoss P a)
    have hScores : scores.Nonempty := by
      rcases hA with ⟨a, ha⟩
      exact ⟨maxLoss P a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    exact Finset.min' scores hScores
  · exact 0

noncomputable def minimax : VotingRule := by
  intro V A _ _ P
  classical
  if Nonempty A then
    let minScore := minimaxScore P
    exact Finset.univ.filter (fun a => maxLoss P a = minScore)
  else
    exact ∅

end Minimax

end SocialChoice
