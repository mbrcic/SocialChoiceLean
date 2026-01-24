import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Rules.SplitCycle.Condorcet
import SocialChoice.Rules.SplitCycle.InformationalBasis
import SocialChoice.Rules.SplitCycle.Pareto
import SocialChoice.Rules.SplitCycle.Reversal

namespace SocialChoice

theorem splitCycle_majority_criterion : MajorityCriterion splitCycle := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := splitCycle)
  · exact splitCycle_isVotingRule
  · exact split_cycle_condorcet_consistency

theorem splitCycle_unanimity : Unanimity splitCycle := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := splitCycle)
  · exact splitCycle_isVotingRule
  · exact split_cycle_pareto_efficiency

theorem splitCycle_majority_loser_criterion : MajorityLoserCriterion splitCycle := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := splitCycle)
  · exact splitCycle_isVotingRule
  · exact split_cycle_CondorcetLoser_criterion

theorem splitCycle_anonymous : Anonymity splitCycle := by
  apply Implies.apply marginBased_implies_anonymity (f := splitCycle)
  · exact splitCycle_isVotingRule
  · exact splitCycle_marginBased

theorem splitCycle_not_subsetReinforcement : ¬ SubsetReinforcement splitCycle := by
  intro hsub
  exact no_condorcet_subset_reinforcement splitCycle
    splitCycle_isVotingRule split_cycle_condorcet_consistency hsub

theorem splitCycle_not_reinforcement : ¬ Reinforcement splitCycle := by
  intro hrein
  exact no_condorcet_reinforcement splitCycle
    splitCycle_isVotingRule split_cycle_condorcet_consistency hrein

end SocialChoice
