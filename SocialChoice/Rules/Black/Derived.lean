import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.Black.CondorcetLoser
import SocialChoice.Rules.Black.InformationalBasis
import SocialChoice.Rules.Black.Neutrality
import SocialChoice.Rules.Black.Pareto

namespace SocialChoice

theorem black_majority_criterion : MajorityCriterion black := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := black)
  · exact black_isVotingRule
  · exact black_condorcet_consistency

theorem black_unanimity : Unanimity black := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := black)
  · exact black_isVotingRule
  · exact black_pareto_efficiency

theorem black_majority_loser_criterion : MajorityLoserCriterion black := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := black)
  · exact black_isVotingRule
  · exact black_CondorcetLoser_criterion

theorem black_anonymous : Anonymity black := by
  apply Implies.apply marginBased_implies_anonymity (f := black)
  · exact black_isVotingRule
  · exact black_marginBased

theorem black_not_subsetReinforcement : ¬ SubsetReinforcement black := by
  intro hsub
  exact no_condorcet_subset_reinforcement black
    black_isVotingRule black_condorcet_consistency hsub

theorem black_not_reinforcement : ¬ Reinforcement black := by
  intro hrein
  exact no_condorcet_reinforcement black
    black_isVotingRule black_condorcet_consistency hrein

theorem black_not_strongFishburnParticipation : ¬ StrongFishburnParticipation black := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨black, black_isVotingRule, black_condorcet_consistency, hpart⟩

theorem black_not_optimistParticipation : ¬ OptimistParticipation black := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨black, black_condorcet_consistency, hpart⟩

end SocialChoice
