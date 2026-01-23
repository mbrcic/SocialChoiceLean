import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.Nanson.Condorcet
import SocialChoice.Rules.Nanson.CondorcetLoser

namespace SocialChoice

theorem nanson_majority_criterion : MajorityCriterion nanson := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := nanson)
  · exact nanson_isVotingRule
  · exact nanson_condorcet_consistency

theorem nanson_unanimity : Unanimity nanson := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := nanson)
  · exact nanson_isVotingRule
  · exact nanson_majority_criterion

theorem nanson_majority_loser_criterion : MajorityLoserCriterion nanson := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := nanson)
  · exact nanson_isVotingRule
  · exact nanson_CondorcetLoser_criterion

theorem nanson_not_subsetReinforcement : ¬ SubsetReinforcement nanson := by
  intro hsub
  exact no_condorcet_subset_reinforcement nanson
    nanson_isVotingRule nanson_condorcet_consistency hsub

theorem nanson_not_reinforcement : ¬ Reinforcement nanson := by
  intro hrein
  exact no_condorcet_reinforcement nanson
    nanson_isVotingRule nanson_condorcet_consistency hrein

end SocialChoice
