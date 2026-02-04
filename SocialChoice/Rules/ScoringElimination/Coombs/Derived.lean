import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringElimination.Anonymity
import SocialChoice.Rules.ScoringElimination.Coombs.Condorcet
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringElimination.Coombs.PositiveInvolvement
import SocialChoice.Rules.ScoringElimination.Coombs.SubsetReinforcement
import SocialChoice.Rules.ScoringElimination.Coombs.Majority
import SocialChoice.Rules.ScoringElimination.Coombs.Pareto
import SocialChoice.Rules.ScoringElimination.Monotonicity
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringRules.Veto.Derived

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

theorem coombs_not_monotonicity : ¬ Monotonicity coombs := by
  have hweak : weaklyDecreasingScore vetoScore := vetoScore_weaklyDecreasing
  have h3 : vetoScore 3 0 > vetoScore 3 2 := by
    decide
  have h2 : vetoScore 2 0 > vetoScore 2 1 := by
    decide
  simpa [coombs] using
      (ScoringEliminationMonotonicityCounterexample.scoringElimination_not_monotonicity
      (score := vetoScore) hweak h3 h2)

theorem coombs_not_subsetReinforcement : ¬ SubsetReinforcement coombs := by
  intro hsub
  have hsubset := hsub (U := Fin 4) (A := Fin 3)
    (V := CoombsSubsetReinforcementCounterexample.voters1)
    (W := CoombsSubsetReinforcementCounterexample.voters2)
    (hdisj := CoombsSubsetReinforcementCounterexample.voters1_disjoint_voters2)
    (P := CoombsSubsetReinforcementCounterexample.profile1)
    (Q := CoombsSubsetReinforcementCounterexample.profile2)
    (R := CoombsSubsetReinforcementCounterexample.profileAll)
    CoombsSubsetReinforcementCounterexample.restrict_profileAll_voters1
    CoombsSubsetReinforcementCounterexample.restrict_profileAll_voters2
  exact CoombsSubsetReinforcementCounterexample.coombs_subsetReinforcement_counterexample_sets hsubset

theorem coombs_not_reinforcement : ¬ Reinforcement coombs := by
  intro hrein
  exact coombs_not_subsetReinforcement (reinforcement_subset hrein)

theorem vetoElimination_majority_loser_criterion :
    MajorityLoserCriterion vetoElimination := by
  intro V A _ _ P c hmaj hne
  simpa [vetoElimination] using
    (coombs_majority_loser_criterion (V := V) (A := A) (P := P) (c := c) hmaj hne)

end SocialChoice
