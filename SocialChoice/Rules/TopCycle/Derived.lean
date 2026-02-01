import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Smith
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.TopCycle.Condorcet
import SocialChoice.Rules.TopCycle.CondorcetLoser
import SocialChoice.Rules.TopCycle.MutualMajority

namespace SocialChoice

/-- TopCycle satisfies the majority criterion (via Condorcet consistency). -/
theorem topCycle_majorityCriterion : MajorityCriterion topCycle := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := topCycle)
  · exact topCycle_isVotingRule
  · exact topCycle_condorcetConsistency

/-- TopCycle satisfies unanimity (via majority criterion). -/
theorem topCycle_unanimity : Unanimity topCycle := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := topCycle)
  · exact topCycle_isVotingRule
  · exact topCycle_majorityCriterion

/-- TopCycle satisfies the majority loser criterion (via Condorcet loser). -/
theorem topCycle_majorityLoserCriterion : MajorityLoserCriterion topCycle := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := topCycle)
  · exact topCycle_isVotingRule
  · exact topCycle_condorcetLoser_criterion

theorem topCycle_smithCriterion : SmithCriterion topCycle := by
  exact Refines.refl topCycle

theorem topCycle_not_subsetReinforcement : ¬ SubsetReinforcement topCycle := by
  intro hsub
  exact no_condorcet_subset_reinforcement topCycle
    topCycle_isVotingRule topCycle_condorcetConsistency hsub

theorem topCycle_not_reinforcement : ¬ Reinforcement topCycle := by
  intro hrein
  exact no_condorcet_reinforcement topCycle
    topCycle_isVotingRule topCycle_condorcetConsistency hrein

theorem topCycle_not_strongFishburnParticipation : ¬ StrongFishburnParticipation topCycle := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨topCycle, topCycle_isVotingRule, topCycle_condorcetConsistency, hpart⟩

theorem topCycle_not_optimistParticipation : ¬ OptimistParticipation topCycle := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨topCycle, topCycle_condorcetConsistency, hpart⟩

end SocialChoice
