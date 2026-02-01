import SocialChoice.Axioms.Implications
import SocialChoice.Rules.PluralityWithRunoff.Condorcet
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.PluralityWithRunoff.Pareto

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

end SocialChoice
