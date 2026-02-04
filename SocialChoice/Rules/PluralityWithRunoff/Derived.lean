import SocialChoice.Axioms.Implications
import SocialChoice.Rules.PluralityWithRunoff.Condorcet
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.PluralityWithRunoff.Involvement
import SocialChoice.Rules.PluralityWithRunoff.Pareto
import SocialChoice.Rules.PluralityWithRunoff.Reversal
import SocialChoice.Rules.PluralityWithRunoff.SubsetReinforcement

namespace SocialChoice

theorem plurality_with_runoff_majority_loser_criterion :
    MajorityLoserCriterion pluralityWithRunoff := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion
    (f := pluralityWithRunoff)
  · exact pluralityWithRunoff_isVotingRule
  · exact plurality_with_runoff_CondorcetLoser_criterion

theorem plurality_with_runoff_unanimity : Unanimity pluralityWithRunoff := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := pluralityWithRunoff)
  · exact pluralityWithRunoff_isVotingRule
  · exact plurality_with_runoff_pareto_efficiency

theorem pluralityWithRunoff_not_smithCriterion : ¬ SmithCriterion pluralityWithRunoff := by
  intro hsmith
  have hcond : CondorcetConsistency pluralityWithRunoff :=
    Implies.apply smithCriterion_implies_condorcetConsistency_Imp
      (f := pluralityWithRunoff) pluralityWithRunoff_isVotingRule hsmith
  exact pluralityWithRunoff_not_condorcet hcond

theorem pluralityWithRunoff_not_reinforcement : ¬ Reinforcement pluralityWithRunoff := by
  intro hrein
  exact pluralityWithRunoff_not_subsetReinforcement (reinforcement_subset hrein)

theorem pluralityWithRunoff_not_reversalSymmetry : ¬ ReversalSymmetry pluralityWithRunoff := by
  intro hrev
  have hsingle : SingletonReversalSymmetry pluralityWithRunoff :=
    Implies.apply reversalSymmetry_implies_singletonReversalSymmetry
      (f := pluralityWithRunoff) pluralityWithRunoff_isVotingRule hrev
  exact pluralityWithRunoff_not_singletonReversalSymmetry hsingle

theorem pluralityWithRunoff_not_strongFishburnParticipation :
    ¬ StrongFishburnParticipation pluralityWithRunoff := by
  intro hpart
  have hneg : NegativeInvolvement pluralityWithRunoff :=
    Implies.apply strongFishburnParticipation_implies_negativeInvolvement
      (f := pluralityWithRunoff) pluralityWithRunoff_isVotingRule hpart
  exact pluralityWithRunoff_not_negativeInvolvement hneg

end SocialChoice
