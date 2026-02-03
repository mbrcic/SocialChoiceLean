import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringElimination.Anonymity
import SocialChoice.Rules.ScoringElimination.Coombs.Condorcet
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringElimination.Coombs.PositiveInvolvement
import SocialChoice.Rules.ScoringElimination.Coombs.Majority
import SocialChoice.Rules.ScoringElimination.Coombs.Pareto
import SocialChoice.Rules.ScoringElimination.Neutrality

namespace SocialChoice

theorem coombs_anonymous : Anonymity coombs := by
  intro V A _ _ P σ
  simpa [coombs] using
    (scoringEliminationRule_anonymous (score := vetoScore) (P := P) (σ := σ))

theorem coombs_neutral : Neutrality coombs := by
  intro V A _ _ P σ
  simpa [coombs] using
    (scoringEliminationRule_neutral (score := vetoScore) (P := P) (σ := σ))

theorem coombs_unanimity : Unanimity coombs := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := coombs)
  · exact coombs_isVotingRule
  · exact coombs_paretoEfficiency

theorem coombs_not_smithCriterion : ¬ SmithCriterion coombs := by
  intro hsmith
  have hcond : CondorcetConsistency coombs :=
    Implies.apply smithCriterion_implies_condorcetConsistency_Imp
      (f := coombs) coombs_isVotingRule hsmith
  exact CoombsCondorcetCounterexample.coombs_not_condorcet hcond

theorem vetoElimination_majority_loser_criterion :
    MajorityLoserCriterion vetoElimination := by
  intro V A _ _ P c hmaj hne
  simpa [vetoElimination] using
    (coombs_majority_loser_criterion (V := V) (A := A) (P := P) (c := c) hmaj hne)

end SocialChoice
