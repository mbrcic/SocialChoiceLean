import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Fin
import SocialChoice.Profile
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Margin

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

/-! Basic scaffolding for Holliday impossibility (5 candidates). -/

abbrev A5 := Fin 5

abbrev a : A5 := 0
abbrev b : A5 := 1
abbrev c : A5 := 2
abbrev d : A5 := 3
abbrev e : A5 := 4

end Holliday

end SocialChoice
