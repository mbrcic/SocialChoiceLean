import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.Black.CondorcetLoser
import SocialChoice.Rules.Black.InformationalBasis
import SocialChoice.Rules.Black.Neutrality
import SocialChoice.Rules.Black.Pareto
import SocialChoice.Rules.Black.SubsetReinforcement
import SocialChoice.Rules.Black.Involvement
import SocialChoice.Rules.Black.Monotonicity
import SocialChoice.Rules.Black.Smith
import SocialChoice.Rules.Black.Reversal

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
  have hsubset := hsub (U := Fin 5) (A := Fin 3)
    (V := BlackSubsetReinforcementCounterexample.voters3)
    (W := BlackSubsetReinforcementCounterexample.voters2)
    (hdisj := BlackSubsetReinforcementCounterexample.voters3_disjoint_voters2)
    (P := BlackSubsetReinforcementCounterexample.profile3)
    (Q := BlackSubsetReinforcementCounterexample.profile2)
    (R := BlackSubsetReinforcementCounterexample.profileAll)
    BlackSubsetReinforcementCounterexample.restrict_profileAll_voters3
    BlackSubsetReinforcementCounterexample.restrict_profileAll_voters2
  exact BlackSubsetReinforcementCounterexample.black_subsetReinforcement_counterexample_sets hsubset

theorem black_not_reinforcement : ¬ Reinforcement black := by
  intro hrein
  exact black_not_subsetReinforcement (reinforcement_subset hrein)

theorem black_not_strongFishburnParticipation : ¬ StrongFishburnParticipation black := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨black, black_isVotingRule, black_condorcet_consistency, hpart⟩

theorem black_not_optimistParticipation : ¬ OptimistParticipation black := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨black, black_condorcet_consistency, hpart⟩

theorem black_not_positiveInvolvement : ¬ PositiveInvolvement black := by
  apply mt (Implies.apply positiveInvolvement_implies_singletonPositiveInvolvement (f := black) black_isVotingRule)
  exact black_not_singletonPositiveInvolvement

theorem black_not_negativeInvolvement : ¬ NegativeInvolvement black := by
  intro hneg
  have hiff : PositiveInvolvement black ↔ NegativeInvolvement black :=
    Implies.apply marginBased_positiveInvolvement_iff_negativeInvolvement
      (f := black) black_isVotingRule black_marginBased
  exact black_not_positiveInvolvement (hiff.mpr hneg)

theorem black_singleton_reversal_symmetry : SingletonReversalSymmetry black := by
  apply Implies.apply reversalSymmetry_implies_singletonReversalSymmetry (f := black)
  · exact black_isVotingRule
  · exact black_reversal_symmetry

end SocialChoice
