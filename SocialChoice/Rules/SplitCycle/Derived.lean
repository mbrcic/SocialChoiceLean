import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.SplitCycle.Smith
import SocialChoice.Rules.SplitCycle.Condorcet
import SocialChoice.Rules.SplitCycle.InformationalBasis
import SocialChoice.Rules.SplitCycle.Independence
import SocialChoice.Rules.SplitCycle.Involvement
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

theorem splitCycle_mutualMajorityCriterion : MutualMajorityCriterion splitCycle := by
  apply Implies.apply smithCriterion_implies_mutualMajorityCriterion_Imp (f := splitCycle)
  · exact splitCycle_isVotingRule
  · exact splitCycle_smithCriterion

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

theorem splitCycle_not_strongFishburnParticipation : ¬ StrongFishburnParticipation splitCycle := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨splitCycle, splitCycle_isVotingRule, split_cycle_condorcet_consistency, hpart⟩

theorem splitCycle_not_optimistParticipation : ¬ OptimistParticipation splitCycle := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨splitCycle, split_cycle_condorcet_consistency, hpart⟩

theorem splitCycle_negative_involvement : NegativeInvolvement splitCycle := by
  exact split_cycle_negative_involvement

end SocialChoice
