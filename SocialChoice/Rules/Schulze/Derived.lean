import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Majority
import SocialChoice.Axioms.Smith
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.Schulze.InformationalBasis
import SocialChoice.Rules.Schulze.Independence
import SocialChoice.Rules.Schulze.Transitivity
import SocialChoice.Rules.Schulze.RefinesSplitCycle
import SocialChoice.Rules.Schulze.Neutrality
import SocialChoice.Rules.SplitCycle.Condorcet
import SocialChoice.Rules.SplitCycle.Pareto
import SocialChoice.Rules.SplitCycle.Reversal
import SocialChoice.Rules.SplitCycle.Smith

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

theorem schulze_smithCriterion : SmithCriterion schulze := by
  apply PreservedUnderRefinement.apply smithCriterion_preservedUnderRefinement
    (f := schulze) (g := splitCycle)
  · exact schulze_isVotingRule
  · exact splitCycle_isVotingRule
  · exact schulze_refines_splitCycle
  · exact splitCycle_smithCriterion

theorem schulze_mutualMajorityCriterion : MutualMajorityCriterion schulze := by
  apply Implies.apply smithCriterion_implies_mutualMajorityCriterion_Imp (f := schulze)
  · exact schulze_isVotingRule
  · exact schulze_smithCriterion

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

theorem schulze_anonymous : Anonymity schulze := by
  apply Implies.apply marginBased_implies_anonymity (f := schulze)
  · exact schulze_isVotingRule
  · exact schulze_marginBased

theorem schulze_not_subsetReinforcement : ¬ SubsetReinforcement schulze := by
  intro hsub
  exact no_condorcet_subset_reinforcement schulze
    schulze_isVotingRule schulze_condorcet_consistency hsub

theorem schulze_not_reinforcement : ¬ Reinforcement schulze := by
  intro hrein
  exact no_condorcet_reinforcement schulze
    schulze_isVotingRule schulze_condorcet_consistency hrein

theorem schulze_not_strongFishburnParticipation : ¬ StrongFishburnParticipation schulze := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨schulze, schulze_isVotingRule, schulze_condorcet_consistency, hpart⟩

theorem schulze_not_optimistParticipation : ¬ OptimistParticipation schulze := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨schulze, schulze_condorcet_consistency, hpart⟩

end SocialChoice
