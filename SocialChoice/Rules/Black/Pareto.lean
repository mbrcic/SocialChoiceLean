import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.ScoringRules.Borda.Pareto

namespace SocialChoice

theorem black_pareto_efficiency : ParetoEfficiency black := by
  intro V A _ _ _ P c d hpref
  classical
  by_cases h : ∃ x, CondorcetWinner P x
  · have hxwin : CondorcetWinner P (Classical.choose h) := Classical.choose_spec h
    have hxne : d ≠ Classical.choose h := by
      intro hEq
      subst hEq
      have hpos2 : margin_pos P c (Classical.choose h) :=
        unanimous_margin (P := P) (x := c) (y := Classical.choose h) (by simpa using hpref)
      have hne : Classical.choose h ≠ c := by
        exact (ne_of_margin_pos (P := P) hpos2).symm
      have hpos1 : margin_pos P (Classical.choose h) c :=
        (CondorcetWinner_iff_margin_pos P (Classical.choose h)).mp hxwin c
          (by simpa [eq_comm] using hne)
      exact (margin_pos_asymm (P := P) _ _ hpos1) hpos2
    simp [black, h, hxne]
  · have hborda : black P = borda P := by
      simp [black, h]
    have hd' : d ∉ borda P :=
      borda_pareto_efficiency (P := P) (c := c) (d := d) hpref
    simpa [hborda] using hd'

end SocialChoice
