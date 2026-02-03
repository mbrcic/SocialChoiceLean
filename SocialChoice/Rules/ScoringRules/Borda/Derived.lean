import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringRules.Anonymity
import SocialChoice.Rules.ScoringRules.Condorcet
import SocialChoice.Rules.ScoringRules.Derived
import SocialChoice.Rules.ScoringRules.Monotonicity
import SocialChoice.Rules.ScoringRules.Neutrality
import SocialChoice.Rules.ScoringRules.Pareto
import SocialChoice.Rules.ScoringRules.Participation
import SocialChoice.Rules.ScoringRules.Reinforcement
import SocialChoice.Rules.ScoringRules.Borda.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.Defs
import SocialChoice.Rules.ScoringRules.Borda.Independence
import SocialChoice.Rules.ScoringRules.Borda.Majority
import SocialChoice.Rules.ScoringRules.Borda.Pareto
import SocialChoice.Rules.ScoringRules.Borda.Reversal

namespace SocialChoice

theorem borda_independenceOfUniversallyLeastPreferred :
    IndependenceOfUniversallyLeastPreferred borda := by
  intro V A _ _ _ _ P c d hcd hbot
  exact borda_independence_of_universally_least_preferred_nonempty
    (P := P) (c := c) (d := d) hcd hbot

theorem borda_unanimity : Unanimity borda := by
  apply Implies.apply paretoEfficiency_implies_unanimity (f := borda)
  · exact borda_isVotingRule
  · exact borda_pareto_efficiency

theorem borda_anonymous : Anonymity borda := by
  intro V A _ _ P σ
  simpa [borda] using (scoringRule_anonymous (score := bordaScore) (P := P) (σ := σ))

theorem borda_neutral : Neutrality borda := by
  intro V A _ _ P σ
  simpa [borda] using (scoringRule_neutral (score := bordaScore) (P := P) (σ := σ))

theorem borda_monotonicity_derived : Monotonicity borda := by
  intro V A _ _ P P' x hx hLift
  have hmono : weaklyDecreasingScore bordaScore :=
    strictlyDecreasingScore.to_weakly (score := bordaScore) bordaScore_strictlyDecreasing
  have hx' : x ∈ scoringRule bordaScore P := by
    simpa [borda] using hx
  have h' :=
    (scoringRule_monotonicity (score := bordaScore) hmono)
      (P := P) (P' := P') (x := x) hx' hLift
  simpa [borda] using h'

theorem borda_reinforcement : Reinforcement borda := by
  intro U A _ _ _ V W hdisj P Q R hRV hRW hnonempty
  have hnonempty' : (scoringRule bordaScore P ∩ scoringRule bordaScore Q).Nonempty := by
    simpa [borda] using hnonempty
  have h :=
    (scoringRule_reinforcement (score := bordaScore))
      (V := V) (W := W) (hdisj := hdisj) (P := P) (Q := Q) (R := R) hRV hRW hnonempty'
  simpa [borda] using h

theorem borda_subsetReinforcement : SubsetReinforcement borda := by
  intro U A _ _ _ V W hdisj P Q R hRV hRW x hx
  have hx' : x ∈ scoringRule bordaScore P ∩ scoringRule bordaScore Q := by
    simpa [borda] using hx
  have h :=
    (scoringRule_subsetReinforcement (score := bordaScore))
      (V := V) (W := W) (hdisj := hdisj) (P := P) (Q := Q) (R := R) hRV hRW
  have hx'' := h hx'
  simpa [borda] using hx''

theorem borda_strongFishburnParticipation : StrongFishburnParticipation borda := by
  intro U A _ _ _ V u hu P Q hagree
  have hmono : weaklyDecreasingScore bordaScore :=
    strictlyDecreasingScore.to_weakly (score := bordaScore) bordaScore_strictlyDecreasing
  have h :=
    (scoringRule_strongFishburnParticipation (score := bordaScore) hmono)
      (V := V) (u := u) (hu := hu) (P := P) (Q := Q) hagree
  simpa [borda] using h

theorem borda_positive_involvement : PositiveInvolvement borda := by
  apply Implies.apply strongFishburnParticipation_implies_positiveInvolvement (f := borda)
  · exact borda_isVotingRule
  · exact borda_strongFishburnParticipation

theorem borda_negative_involvement : NegativeInvolvement borda := by
  apply Implies.apply strongFishburnParticipation_implies_negativeInvolvement (f := borda)
  · exact borda_isVotingRule
  · exact borda_strongFishburnParticipation

theorem borda_pareto : ParetoEfficiency borda := by
  intro V A _ _ _ P c d hpref
  have h :=
    (scoringRule_pareto_nonempty (score := bordaScore) bordaScore_strictlyDecreasing)
      (P := P) (c := c) (d := d) hpref
  simpa [borda] using h

theorem borda_not_condorcet : ¬ CondorcetConsistency borda := by
  simpa [borda] using (scoringRule_not_condorcet (score := bordaScore))

theorem borda_not_smithCriterion : ¬ SmithCriterion borda := by
  intro hsmith
  have hcond : CondorcetConsistency borda :=
    Implies.apply smithCriterion_implies_condorcetConsistency_Imp
      (f := borda) borda_isVotingRule hsmith
  exact borda_not_condorcet hcond

theorem borda_singleton_reversal_symmetry : SingletonReversalSymmetry borda := by
  apply Implies.apply reversalSymmetry_implies_singletonReversalSymmetry (f := borda)
  · exact borda_isVotingRule
  · exact borda_reversal_symmetry

theorem borda_majority_loser_criterion : MajorityLoserCriterion borda := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := borda)
  · exact borda_isVotingRule
  · exact borda_CondorcetLoser_criterion

theorem borda_not_mutualMajorityCriterion : ¬ MutualMajorityCriterion borda := by
  intro hmut
  have hmaj : MajorityCriterion borda :=
    Implies.apply mutualMajorityCriterion_implies_majorityCriterion_Imp
      (f := borda) borda_isVotingRule hmut
  exact borda_not_majority_criterion hmaj

end SocialChoice
