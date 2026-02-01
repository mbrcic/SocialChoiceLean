import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Cycles
import SocialChoice.Meta

namespace SocialChoice

open Finset

/-- Weight of a margin edge. -/
noncomputable def edgeWeight {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (e : A × A) : Int :=
  margin P e.1 e.2

/-- Margin edges: all ordered pairs with nonnegative margin. -/
noncomputable def marginEdges {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : Finset (A × A) := by
  classical
  exact Finset.univ.filter (fun e => 0 <= edgeWeight P e)

/-- A list of edges is descending if margins are nonincreasing along the list. -/
def descendingEdges {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (tau : List (A × A)) : Prop :=
  tau.Pairwise (fun e1 e2 => edgeWeight P e1 >= edgeWeight P e2)

/-- Tiebreakers are descending linear orderings of the margin edges. -/
def isTiebreaker {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (tau : List (A × A)) : Prop :=
by
  classical
  exact tau.Nodup ∧ tau.toFinset = marginEdges P ∧ descendingEdges P tau

/-- Edge relation induced by a finset of edges. -/
def edgeRel {A : Type} (E : Finset (A × A)) : A → A → Prop :=
  fun a b => (a, b) ∈ E

/-- `y` has an incoming edge in `E`. -/
def hasIncoming {A : Type} (E : Finset (A × A)) (y : A) : Prop :=
  ∃ x, (x, y) ∈ E

/-- The edge set `E` contains a directed cycle. -/
def hasCycle {A : Type} (E : Finset (A × A)) : Prop :=
  ∃ c : List A, cycle (edgeRel (A := A) E) c

/-- Add an edge unless it violates the branching or cycle condition. -/
noncomputable def riverAddEdge {A : Type}
    (E : Finset (A × A)) (e : A × A) : Finset (A × A) := by
  classical
  exact if hasIncoming (A := A) E e.2 ∨ hasCycle (A := A) (insert e E)
    then E else insert e E

/-- The River diagram (edge set) obtained by processing edges in order. -/
noncomputable def riverDiagram {A : Type} (tau : List (A × A)) : Finset (A × A) := by
  classical
  exact tau.foldl (riverAddEdge (A := A)) (Finset.empty : Finset (A × A))

/-- Winners for a fixed tiebreaker: vertices with no incoming edges in the diagram. -/
noncomputable def riverWinners {A : Type} [Fintype A] (tau : List (A × A)) : Finset A := by
  classical
  let E := riverDiagram (A := A) tau
  exact Finset.univ.filter (fun a => ¬ hasIncoming (A := A) E a)

/-- River (PUT): union of winners over all descending tiebreakers. -/
@[scRule]
noncomputable def river : VotingRule := by
  intro V A _ _ P
  classical
  exact Finset.univ.filter (fun a =>
    ∃ tau : List (A × A), isTiebreaker (P := P) tau ∧ a ∈ riverWinners (A := A) tau)

end SocialChoice
