import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.Nanson.Condorcet
import SocialChoice.Rules.Nanson.CondorcetLoser
import SocialChoice.Rules.Nanson.InformationalBasis
import SocialChoice.Rules.Nanson.Reversal
import SocialChoice.Rules.Nanson.Neutrality

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

theorem nanson_anonymous : Anonymity nanson := by
  apply Implies.apply marginBased_implies_anonymity (f := nanson)
  · exact nanson_isVotingRule
  · exact nanson_marginBased

theorem nanson_not_subsetReinforcement : ¬ SubsetReinforcement nanson := by
  intro hsub
  exact no_condorcet_subset_reinforcement nanson
    nanson_isVotingRule nanson_condorcet_consistency hsub

theorem nanson_not_reinforcement : ¬ Reinforcement nanson := by
  intro hrein
  exact no_condorcet_reinforcement nanson
    nanson_isVotingRule nanson_condorcet_consistency hrein

theorem nanson_not_strongFishburnParticipation : ¬ StrongFishburnParticipation nanson := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨nanson, nanson_isVotingRule, nanson_condorcet_consistency, hpart⟩

theorem nanson_not_optimistParticipation : ¬ OptimistParticipation nanson := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨nanson, nanson_condorcet_consistency, hpart⟩

theorem nanson_singleton_reversal_symmetry : SingletonReversalSymmetry nanson := by
  apply Implies.apply reversalSymmetry_implies_singletonReversalSymmetry (f := nanson)
  · exact nanson_isVotingRule
  · exact nanson_reversal_symmetry

end SocialChoice
