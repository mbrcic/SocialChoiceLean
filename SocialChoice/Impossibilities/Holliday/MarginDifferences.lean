import Mathlib.Tactic
import SocialChoice.Impossibilities.Holliday.Margins

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

-- Edge weights in the margin graph for P1 (positive margins only).
def edgeWeights_P1 : Finset Int := {84, 86, 2, 46, 42, 92, 44, 88, 8}

-- Edge weights in the margin graphs for P3 and P5 (positive margins only).
def edgeWeights_P3 : Finset Int := {63, 107, 35, 67, 75, 19, 59, 23, 55, 13}

def edgeWeights_P5 : Finset Int := {80, 138, 18, 36, 92, 12, 42, 6, 24, 30}

lemma edgeWeights_P1_gap2 :
    ∀ m ∈ edgeWeights_P1, ∀ n ∈ edgeWeights_P1, m ≠ n →
      2 ≤ Int.natAbs (m - n) := by
  decide

lemma edgeWeights_P3_gap4 :
    ∀ m ∈ edgeWeights_P3, ∀ n ∈ edgeWeights_P3, m ≠ n →
      4 ≤ Int.natAbs (m - n) := by
  decide

lemma edgeWeights_P5_gap6 :
    ∀ m ∈ edgeWeights_P5, ∀ n ∈ edgeWeights_P5, m ≠ n →
      6 ≤ Int.natAbs (m - n) := by
  decide

end Holliday

end SocialChoice
