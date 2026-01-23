import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringRules.Defs
import SocialChoice.Rules.ScoringRules.Pareto
import SocialChoice.Rules.ScoringRules.Reinforcement

namespace SocialChoice

theorem scoringRule_unanimity (score : Nat → Nat → Int)
    (hstrict : strictlyDecreasingScore score) :
    Unanimity (scoringRule score) := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := scoringRule score)
  · exact scoringRule_isVotingRule score
  · exact scoringRule_pareto_nonempty score hstrict

theorem scoringRule_subsetReinforcement (score : Nat → Nat → Int) :
    SubsetReinforcement (scoringRule score) := by
  apply Implies.apply reinforcement_implies_subsetReinforcement (f := scoringRule score)
  · exact scoringRule_isVotingRule score
  · exact scoringRule_reinforcement score

end SocialChoice
