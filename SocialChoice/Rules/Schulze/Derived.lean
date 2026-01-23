import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Majority
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Rules.Schulze.Transitivity
import SocialChoice.Rules.Schulze.RefinesSplitCycle
import SocialChoice.Rules.SplitCycle.Condorcet
import SocialChoice.Rules.SplitCycle.Pareto
import SocialChoice.Rules.SplitCycle.Reversal

namespace SocialChoice

/-! ## Axioms Derived From SplitCycle Refinement -/

theorem schulze_pareto_efficiency : ParetoEfficiency schulze := by
  apply PreservedUnderRefinement.apply paretoEfficiency_preservedUnderRefinement
    (f := schulze) (g := splitCycle)
  · exact schulze_isVotingRule
  · exact splitCycle_isVotingRule
  · exact schulze_refines_splitCycle
  · exact split_cycle_pareto_efficiency

theorem schulze_condorcet_consistency : CondorcetConsistency schulze := by
  apply PreservedUnderRefinement.apply condorcetConsistency_preservedUnderRefinement
    (f := schulze) (g := splitCycle)
  · exact schulze_isVotingRule
  · exact splitCycle_isVotingRule
  · exact schulze_refines_splitCycle
  · exact split_cycle_condorcet_consistency

theorem schulze_condorcetLoser_criterion : CondorcetLoserCriterion schulze := by
  apply PreservedUnderRefinement.apply condorcetLoserCriterion_preservedUnderRefinement
    (f := schulze) (g := splitCycle)
  · exact schulze_isVotingRule
  · exact splitCycle_isVotingRule
  · exact schulze_refines_splitCycle
  · exact split_cycle_CondorcetLoser_criterion

/-! ## Axioms Derived Through Implications -/

theorem schulze_majority_criterion : MajorityCriterion schulze := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := schulze)
  · exact schulze_isVotingRule
  · exact schulze_condorcet_consistency

theorem schulze_unanimity : Unanimity schulze := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := schulze)
  · exact schulze_isVotingRule
  · exact schulze_pareto_efficiency

theorem schulze_majority_loser_criterion : MajorityLoserCriterion schulze := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := schulze)
  · exact schulze_isVotingRule
  · exact schulze_condorcetLoser_criterion

theorem schulze_not_subsetReinforcement : ¬ SubsetReinforcement schulze := by
  intro hsub
  exact no_condorcet_subset_reinforcement schulze
    schulze_isVotingRule schulze_condorcet_consistency hsub

theorem schulze_not_reinforcement : ¬ Reinforcement schulze := by
  intro hrein
  exact no_condorcet_reinforcement schulze
    schulze_isVotingRule schulze_condorcet_consistency hrein

end SocialChoice
