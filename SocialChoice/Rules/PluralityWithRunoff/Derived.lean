import SocialChoice.Axioms.Implications
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser

namespace SocialChoice

theorem plurality_with_runoff_majority_loser_criterion :
    MajorityLoserCriterion pluralityWithRunoff := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion
    (f := pluralityWithRunoff)
  · exact pluralityWithRunoff_isVotingRule
  · exact plurality_with_runoff_CondorcetLoser_criterion

end SocialChoice
