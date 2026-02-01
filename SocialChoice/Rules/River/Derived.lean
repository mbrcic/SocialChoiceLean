import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Majority
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.River.Basic
import SocialChoice.Rules.River.RefinesSplitCycle
import SocialChoice.Rules.SplitCycle.Condorcet
import SocialChoice.Rules.SplitCycle.Pareto
import SocialChoice.Rules.SplitCycle.Reversal

namespace SocialChoice

/-! ## Axioms Derived From SplitCycle Refinement -/

theorem river_pareto_efficiency : ParetoEfficiency river := by
  apply PreservedUnderRefinement.apply paretoEfficiency_preservedUnderRefinement
    (f := river) (g := splitCycle)
  · exact river_isVotingRule
  · exact splitCycle_isVotingRule
  · exact river_refines_splitCycle
  · exact split_cycle_pareto_efficiency

theorem river_condorcet_consistency : CondorcetConsistency river := by
  apply PreservedUnderRefinement.apply condorcetConsistency_preservedUnderRefinement
    (f := river) (g := splitCycle)
  · exact river_isVotingRule
  · exact splitCycle_isVotingRule
  · exact river_refines_splitCycle
  · exact split_cycle_condorcet_consistency

theorem river_condorcetLoser_criterion : CondorcetLoserCriterion river := by
  apply PreservedUnderRefinement.apply condorcetLoserCriterion_preservedUnderRefinement
    (f := river) (g := splitCycle)
  · exact river_isVotingRule
  · exact splitCycle_isVotingRule
  · exact river_refines_splitCycle
  · exact split_cycle_CondorcetLoser_criterion

/-! ## Axioms Derived Through Implications -/

theorem river_majority_criterion : MajorityCriterion river := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := river)
  · exact river_isVotingRule
  · exact river_condorcet_consistency

theorem river_unanimity : Unanimity river := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := river)
  · exact river_isVotingRule
  · exact river_pareto_efficiency

theorem river_majority_loser_criterion : MajorityLoserCriterion river := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := river)
  · exact river_isVotingRule
  · exact river_condorcetLoser_criterion

theorem river_not_subsetReinforcement : ¬ SubsetReinforcement river := by
  intro hsub
  exact no_condorcet_subset_reinforcement river
    river_isVotingRule river_condorcet_consistency hsub

theorem river_not_reinforcement : ¬ Reinforcement river := by
  intro hrein
  exact no_condorcet_reinforcement river
    river_isVotingRule river_condorcet_consistency hrein

theorem river_not_strongFishburnParticipation : ¬ StrongFishburnParticipation river := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨river, river_isVotingRule, river_condorcet_consistency, hpart⟩

theorem river_not_optimistParticipation : ¬ OptimistParticipation river := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨river, river_condorcet_consistency, hpart⟩

end SocialChoice
