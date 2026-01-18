import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

theorem borda_CondorcetLoser_criterion : CondorcetLoserCriterion borda := by
  intro V A _ _ P x hlose
  by_contra hx
  have hb : borda P = c2BordaRule P := borda_eq_c2BordaRule (P := P)
  have hx' : x ∈ c2BordaRule P := by
    simpa [hb] using hx
  have hnonneg : 0 ≤ c2BordaScore P x := c2BordaRule_score_nonneg (P := P) hx'
  have hneg : c2BordaScore P x < 0 :=
    c2BordaScore_neg_of_CondorcetLoser (P := P) (x := x) hlose
  exact (not_lt_of_ge hnonneg) hneg

end SocialChoice
