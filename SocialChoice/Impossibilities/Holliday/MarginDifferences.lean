import Mathlib.Tactic
import SocialChoice.Impossibilities.Holliday.Margins

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

-- Edge weights in the margin graph for P1 (positive margins only).
def edgeWeights_P1 : Finset Int := {81, 83, 1, 47, 37, 91, 41, 87, 5}

-- Edge weights in the margin graphs for P3 and P5 (positive margins only).
def edgeWeights_P3 : Finset Int := {62, 102, 34, 66, 70, 18, 58, 22, 54, 14}

def edgeWeights_P5 : Finset Int := {78, 118, 18, 36, 86, 12, 42, 6, 24, 30}

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
