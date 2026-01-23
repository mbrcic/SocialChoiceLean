import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringElimination.Anonymity
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.MutualMajority

namespace SocialChoice

theorem instantRunoffVoting_anonymous : Anonymity instantRunoffVoting := by
  intro V A _ _ P σ
  simpa [instantRunoffVoting] using
    (scoringEliminationRule_anonymous (score := pluralityScore) (P := P) (σ := σ))

theorem instantRunoffVoting_neutral : Neutrality instantRunoffVoting := by
  intro V A _ _ P σ
  simpa [instantRunoffVoting] using
    (scoringEliminationRule_neutral (score := pluralityScore) (P := P) (σ := σ))

theorem instantRunoffVoting_majority_criterion : MajorityCriterion instantRunoffVoting := by
  apply Implies.apply mutualMajorityCriterion_implies_majorityCriterion_Imp
    (f := instantRunoffVoting)
  · exact instantRunoffVoting_isVotingRule
  · exact irv_mutual_majority_criterion

theorem instantRunoffVoting_majority_loser_criterion :
    MajorityLoserCriterion instantRunoffVoting := by
  apply Implies.apply mutualMajorityCriterion_implies_majorityLoserCriterion_Imp
    (f := instantRunoffVoting)
  · exact instantRunoffVoting_isVotingRule
  · exact irv_mutual_majority_criterion

theorem instantRunoffVoting_unanimity : Unanimity instantRunoffVoting := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := instantRunoffVoting)
  · exact instantRunoffVoting_isVotingRule
  · exact instantRunoffVoting_majority_criterion

end SocialChoice
