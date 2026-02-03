import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.UncoveredSet.Smith
import SocialChoice.Rules.UncoveredSet.InformationalBasis
import SocialChoice.Rules.UncoveredSet.Involvement
import SocialChoice.Rules.UncoveredSet.Independence
import SocialChoice.Rules.UncoveredSet.Monotonicity

namespace SocialChoice

theorem uncoveredSet_mutualMajorityCriterion : MutualMajorityCriterion UncoveredSet := by
  apply Implies.apply smithCriterion_implies_mutualMajorityCriterion_Imp (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact UncoveredSet_smithCriterion

theorem uncoveredSet_condorcetConsistency : CondorcetConsistency UncoveredSet := by
  apply Implies.apply smithCriterion_implies_condorcetConsistency_Imp (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact UncoveredSet_smithCriterion

theorem uncoveredSet_condorcetLoserCriterion : CondorcetLoserCriterion UncoveredSet := by
  apply Implies.apply smithCriterion_implies_condorcetLoserCriterion_Imp (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact UncoveredSet_smithCriterion

theorem uncoveredSet_majorityCriterion : MajorityCriterion UncoveredSet := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact uncoveredSet_condorcetConsistency

theorem uncoveredSet_unanimity : Unanimity UncoveredSet := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact uncoveredSet_majorityCriterion

theorem uncoveredSet_majorityLoserCriterion : MajorityLoserCriterion UncoveredSet := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact uncoveredSet_condorcetLoserCriterion

theorem uncoveredSet_anonymous : Anonymity UncoveredSet := by
  apply Implies.apply marginBased_implies_anonymity (f := UncoveredSet)
  · exact UncoveredSet_isVotingRule
  · exact UncoveredSet_marginBased

theorem uncoveredSet_not_subsetReinforcement : ¬ SubsetReinforcement UncoveredSet := by
  intro hsub
  exact no_condorcet_subset_reinforcement UncoveredSet
    UncoveredSet_isVotingRule uncoveredSet_condorcetConsistency hsub

theorem uncoveredSet_not_reinforcement : ¬ Reinforcement UncoveredSet := by
  intro hrein
  exact no_condorcet_reinforcement UncoveredSet
    UncoveredSet_isVotingRule uncoveredSet_condorcetConsistency hrein

theorem uncoveredSet_not_strongFishburnParticipation :
    ¬ StrongFishburnParticipation UncoveredSet := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨UncoveredSet, UncoveredSet_isVotingRule, uncoveredSet_condorcetConsistency, hpart⟩

theorem uncoveredSet_not_optimistParticipation : ¬ OptimistParticipation UncoveredSet := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨UncoveredSet, uncoveredSet_condorcetConsistency, hpart⟩

theorem uncoveredSet_not_positiveInvolvement : ¬ PositiveInvolvement UncoveredSet := by
  intro hpos
  have hiff : PositiveInvolvement UncoveredSet ↔ NegativeInvolvement UncoveredSet :=
    Implies.apply marginBased_positiveInvolvement_iff_negativeInvolvement
      (f := UncoveredSet) UncoveredSet_isVotingRule UncoveredSet_marginBased
  exact uncoveredSet_not_negativeInvolvement (hiff.mp hpos)

end SocialChoice
