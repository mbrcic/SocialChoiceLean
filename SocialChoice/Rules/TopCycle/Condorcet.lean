import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

/-- TopCycle (Smith set) satisfies Condorcet consistency. -/
theorem topCycle_condorcetConsistency : CondorcetConsistency topCycle := by
  intro V A _ _ P c hcw
  classical
  have hA : Nonempty A := ⟨c⟩
  have hdom : dominatesSet P ({c} : Finset A) := by
    refine ⟨?_, ?_⟩
    · simp
    · intro a ha b hb
      have ha' : a = c := by
        simpa using ha
      subst ha'
      have hb' : b ≠ a := by
        simpa using hb
      have hpos : ∀ d, a ≠ d → margin_pos P a d :=
        (CondorcetWinner_iff_margin_pos P a).1 hcw
      exact hpos b hb'.symm
  have hsubset : topCycleSet (P := P) ⊆ ({c} : Finset A) :=
    topCycleSet_subset_of_dominates (P := P) hdom
  have hnonempty : (topCycleSet (P := P)).Nonempty :=
    (topCycleSet_dominates (P := P)).1
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A) := hsubset hx
    simpa using this
  have hc : c ∈ topCycleSet (P := P) := by
    simpa [hx'] using hx
  have hsup : ({c} : Finset A) ⊆ topCycleSet (P := P) := by
    intro y hy
    have hy' : y = c := by
      simpa using hy
    subst hy'
    exact hc
  have hEq : topCycleSet (P := P) = ({c} : Finset A) := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      exact hsubset hy
    · intro hy
      exact hsup hy
  simp [topCycle, hA, hEq]

end SocialChoice
