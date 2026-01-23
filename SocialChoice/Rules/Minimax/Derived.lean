import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Rules.Minimax.Defs
import SocialChoice.Rules.Minimax.Condorcet

namespace SocialChoice

theorem minimax_majority_criterion : MajorityCriterion minimax := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := minimax)
  · exact minimax_isVotingRule
  · exact minimax_condorcet_consistency

theorem minimax_unanimity : Unanimity minimax := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := minimax)
  · exact minimax_isVotingRule
  · exact minimax_majority_criterion

theorem minimax_not_subsetReinforcement : ¬ SubsetReinforcement minimax := by
  intro hsub
  exact no_condorcet_subset_reinforcement minimax
    minimax_isVotingRule minimax_condorcet_consistency hsub

theorem minimax_not_reinforcement : ¬ Reinforcement minimax := by
  intro hrein
  exact no_condorcet_reinforcement minimax
    minimax_isVotingRule minimax_condorcet_consistency hrein

end SocialChoice
