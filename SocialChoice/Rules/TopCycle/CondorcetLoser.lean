import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

/-- TopCycle (Smith set) satisfies the Condorcet loser criterion. -/
theorem topCycle_condorcetLoser_criterion : CondorcetLoserCriterion topCycle := by
  intro V A _ _ P c hloser
  classical
  rcases hloser.2 with ⟨d, hdc⟩
  have hA : Nonempty A := ⟨d⟩
  let _ : Nonempty A := hA
  have hloser' : ∀ d, c ≠ d → margin_pos P d c :=
    (CondorcetLoser_iff_margin_pos P c).1 hloser |>.1
  let S : Finset A := Finset.univ.filter (fun x => x ≠ c)
  have hSdom : dominatesSet P S := by
    refine ⟨?_, ?_⟩
    · refine ⟨d, ?_⟩
      simp [S, hdc]
    · intro a ha b hb
      have ha' : a ≠ c := (Finset.mem_filter.mp ha).2
      have hb' : b = c := by
        by_contra hbc
        have : b ∈ S := by
          simp [S, hbc]
        exact hb this
      subst hb'
      exact hloser' a (by simpa [eq_comm] using ha')
  have hsubset : topCycleSet (P := P) ⊆ S :=
    topCycleSet_subset_of_dominates (P := P) hSdom
  have hc_not : c ∉ topCycleSet (P := P) := by
    intro hc
    have : c ∈ S := hsubset hc
    simp [S] at this
  simpa [topCycle, hA] using hc_not

end SocialChoice
