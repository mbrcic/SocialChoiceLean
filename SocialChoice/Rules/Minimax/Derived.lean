import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.Minimax.Defs
import SocialChoice.Rules.Minimax.Condorcet
import SocialChoice.Rules.Minimax.CondorcetLoser
import SocialChoice.Rules.Minimax.InformationalBasis
import SocialChoice.Rules.Minimax.Involvement
import SocialChoice.Rules.Minimax.Neutrality

namespace SocialChoice

theorem minimax_majority_criterion : MajorityCriterion minimax := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := minimax)
  · exact minimax_isVotingRule
  · exact minimax_condorcet_consistency

theorem minimax_unanimity : Unanimity minimax := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := minimax)
  · exact minimax_isVotingRule
  · exact minimax_majority_criterion

theorem minimax_anonymous : Anonymity minimax := by
  apply Implies.apply marginBased_implies_anonymity (f := minimax)
  · exact minimax_isVotingRule
  · exact minimax_marginBased

theorem minimax_negative_involvement : NegativeInvolvement minimax := by
  have hiff :
      PositiveInvolvement (fun {V A} [Fintype V] [Fintype A] => minimax) ↔
      NegativeInvolvement (fun {V A} [Fintype V] [Fintype A] => minimax) := by
    simpa using
      (marginBased_positiveInvolvement_iff_negativeInvolvement minimax
        minimax_isVotingRule minimax_marginBased)
  -- align the goal to the eta‑expanded form
  change NegativeInvolvement (fun {V A} [Fintype V] [Fintype A] => minimax)
  exact hiff.mp minimax_positive_involvement

theorem minimax_not_subsetReinforcement : ¬ SubsetReinforcement minimax := by
  intro hsub
  exact no_condorcet_subset_reinforcement minimax
    minimax_isVotingRule minimax_condorcet_consistency hsub

theorem minimax_not_reinforcement : ¬ Reinforcement minimax := by
  intro hrein
  exact no_condorcet_reinforcement minimax
    minimax_isVotingRule minimax_condorcet_consistency hrein

theorem minimax_not_strongFishburnParticipation : ¬ StrongFishburnParticipation minimax := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨minimax, minimax_isVotingRule, minimax_condorcet_consistency, hpart⟩

theorem minimax_not_optimistParticipation : ¬ OptimistParticipation minimax := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨minimax, minimax_condorcet_consistency, hpart⟩

theorem minimax_not_smithCriterion : ¬ SmithCriterion minimax := by
  intro hsmith
  have hcondLoser : CondorcetLoserCriterion minimax :=
    Implies.apply smithCriterion_implies_condorcetLoserCriterion_Imp
      (f := minimax) minimax_isVotingRule hsmith
  exact minimax_not_condorcetLoser_criterion hcondLoser

end SocialChoice
