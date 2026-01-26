import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringRules.Defs
import SocialChoice.Rules.ScoringRules.Pareto
import SocialChoice.Rules.ScoringRules.Participation
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

theorem scoringRule_positive_involvement (score : Nat → Nat → Int)
    (hmono : weaklyDecreasingScore score) :
    PositiveInvolvement (scoringRule score) := by
  apply Implies.apply strongFishburnParticipation_implies_positiveInvolvement
    (f := scoringRule score)
  · exact scoringRule_isVotingRule score
  · exact scoringRule_strongFishburnParticipation (score := score) hmono

theorem scoringRule_negative_involvement (score : Nat → Nat → Int)
    (hmono : weaklyDecreasingScore score) :
    NegativeInvolvement (scoringRule score) := by
  apply Implies.apply strongFishburnParticipation_implies_negativeInvolvement
    (f := scoringRule score)
  · exact scoringRule_isVotingRule score
  · exact scoringRule_strongFishburnParticipation (score := score) hmono

end SocialChoice
