import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.ScoringRules.Borda.Pareto

namespace SocialChoice

theorem black_pareto : ParetoEfficiency black := by
  intro V A _ _ _ P c d hpref hd
  classical
  by_cases h : ∃ x, condorcet_winner P x
  · have hxwin : condorcet_winner P (Classical.choose h) := Classical.choose_spec h
    have hxne : d ≠ Classical.choose h := by
      intro hEq
      subst hEq
      have hne : c ≠ Classical.choose h := by
        intro hEq'
        subst hEq'
        rcases Classical.choice (inferInstance : Nonempty V) with v0
        have hlt : Prefers P v0 (Classical.choose h) (Classical.choose h) := by
          simpa using hpref v0
        let _ := P.pref v0
        exact (lt_irrefl _ hlt)
      have hpos1 : margin_pos P (Classical.choose h) c :=
        hxwin c (by simpa [eq_comm] using hne)
      have hpos2 : margin_pos P c (Classical.choose h) :=
        unanimous_margin (P := P) (x := c) (y := Classical.choose h) (by simpa using hpref)
      exact (margin_pos_asymm (P := P) _ _ hpos1) hpos2
    simp [black, h, hxne] at hd
  · have hborda : black P = borda P := by
      simp [black, h]
    have hd' : d ∈ borda P := by
      simpa [hborda] using hd
    exact borda_pareto (P := P) (c := c) (d := d) hpref hd'

end SocialChoice
