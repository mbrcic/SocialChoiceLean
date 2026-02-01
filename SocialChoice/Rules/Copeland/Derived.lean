import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.Copeland.Defs
import SocialChoice.Rules.Copeland.Condorcet
import SocialChoice.Rules.Copeland.CondorcetLoser
import SocialChoice.Rules.Copeland.Smith
import SocialChoice.Rules.Copeland.InformationalBasis
import SocialChoice.Rules.Copeland.Involvement

namespace SocialChoice

theorem copeland_mutualMajorityCriterion : MutualMajorityCriterion copeland := by
  apply Implies.apply smithCriterion_implies_mutualMajorityCriterion_Imp (f := copeland)
  · exact copeland_isVotingRule
  · exact copeland_smithCriterion

theorem copeland_majority_criterion : MajorityCriterion copeland := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := copeland)
  · exact copeland_isVotingRule
  · exact copeland_condorcet_consistency

theorem copeland_unanimity : Unanimity copeland := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := copeland)
  · exact copeland_isVotingRule
  · exact copeland_majority_criterion

theorem copeland_majority_loser_criterion : MajorityLoserCriterion copeland := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := copeland)
  · exact copeland_isVotingRule
  · exact copeland_CondorcetLoser_criterion

theorem copeland_anonymous : Anonymity copeland := by
  apply Implies.apply marginBased_implies_anonymity (f := copeland)
  · exact copeland_isVotingRule
  · exact copeland_marginBased

theorem copeland_not_subsetReinforcement : ¬ SubsetReinforcement copeland := by
  intro hsub
  exact no_condorcet_subset_reinforcement copeland
    copeland_isVotingRule copeland_condorcet_consistency hsub

theorem copeland_not_reinforcement : ¬ Reinforcement copeland := by
  intro hrein
  exact no_condorcet_reinforcement copeland
    copeland_isVotingRule copeland_condorcet_consistency hrein

theorem copeland_not_strongFishburnParticipation : ¬ StrongFishburnParticipation copeland := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨copeland, copeland_isVotingRule, copeland_condorcet_consistency, hpart⟩

theorem copeland_not_optimistParticipation : ¬ OptimistParticipation copeland := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨copeland, copeland_condorcet_consistency, hpart⟩

theorem copeland_not_negativeInvolvement : ¬ NegativeInvolvement copeland := by
  intro hneg
  have hiff : PositiveInvolvement copeland ↔ NegativeInvolvement copeland :=
    Implies.apply marginBased_positiveInvolvement_iff_negativeInvolvement
      (f := copeland) copeland_isVotingRule copeland_marginBased
  exact copeland_not_positiveInvolvement (hiff.mpr hneg)

end SocialChoice
