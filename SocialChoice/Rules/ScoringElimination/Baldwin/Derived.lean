import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.ScoringElimination.Anonymity
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringElimination.Baldwin.Condorcet
import SocialChoice.Rules.ScoringElimination.Baldwin.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.Neutrality

namespace SocialChoice

theorem baldwin_anonymous : Anonymity baldwin := by
  intro V A _ _ P σ
  simpa [baldwin] using
    (scoringEliminationRule_anonymous (score := bordaScore) (P := P) (σ := σ))

theorem baldwin_neutral : Neutrality baldwin := by
  intro V A _ _ P σ
  simpa [baldwin] using
    (scoringEliminationRule_neutral (score := bordaScore) (P := P) (σ := σ))

theorem baldwin_majority_criterion : MajorityCriterion baldwin := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := baldwin)
  · exact baldwin_isVotingRule
  · exact baldwin_condorcet_consistency

theorem baldwin_unanimity : Unanimity baldwin := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := baldwin)
  · exact baldwin_isVotingRule
  · exact baldwin_majority_criterion

theorem baldwin_majority_loser_criterion : MajorityLoserCriterion baldwin := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := baldwin)
  · exact baldwin_isVotingRule
  · exact baldwin_CondorcetLoser_criterion

theorem baldwin_not_subsetReinforcement : ¬ SubsetReinforcement baldwin := by
  intro hsub
  exact no_condorcet_subset_reinforcement baldwin
    baldwin_isVotingRule baldwin_condorcet_consistency hsub

theorem baldwin_not_reinforcement : ¬ Reinforcement baldwin := by
  intro hrein
  exact no_condorcet_reinforcement baldwin
    baldwin_isVotingRule baldwin_condorcet_consistency hrein

theorem baldwin_not_strongFishburnParticipation : ¬ StrongFishburnParticipation baldwin := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨baldwin, baldwin_isVotingRule, baldwin_condorcet_consistency, hpart⟩

theorem bordaElimination_majority_criterion : MajorityCriterion bordaElimination := by
  intro V A _ _ P c hmaj
  simpa [bordaElimination] using
    (baldwin_majority_criterion (V := V) (A := A) (P := P) (c := c) hmaj)

theorem bordaElimination_unanimity : Unanimity bordaElimination := by
  intro V A _ _ _ P c htop
  simpa [bordaElimination] using
    (baldwin_unanimity (V := V) (A := A) (P := P) (c := c) htop)

theorem bordaElimination_majority_loser_criterion :
    MajorityLoserCriterion bordaElimination := by
  intro V A _ _ P c hmaj hne
  simpa [bordaElimination] using
    (baldwin_majority_loser_criterion
      (V := V) (A := A) (P := P) (c := c) hmaj hne)

end SocialChoice
