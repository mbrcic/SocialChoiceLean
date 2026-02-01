import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringElimination.Anonymity
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Independence
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.MutualMajority
import SocialChoice.Rules.PluralityWithRunoff.Involvement
import SocialChoice.Rules.PluralityWithRunoff.Monotonicity
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.PluralityWithRunoff.SubsetReinforcement

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

theorem instantRunoffVoting_paretoEfficiency : ParetoEfficiency instantRunoffVoting := by
  apply Implies.apply independenceOfDominated_implies_paretoEfficiency
    (f := instantRunoffVoting)
  · exact instantRunoffVoting_isVotingRule
  · exact instantRunoffVoting_independenceOfDominated

theorem instantRunoffVoting_not_monotonicity : ¬ Monotonicity instantRunoffVoting := by
  simpa using
    (PluralityWithRunoffMonotonicityCounterexample.instantRunoffVoting_not_monotonicity)

theorem instantRunoffVoting_not_negativeInvolvement :
    ¬ NegativeInvolvement instantRunoffVoting := by
  intro hneg
  classical
  have hIRV5 :
      instantRunoffVoting PluralityWithRunoffNegativeInvolvementCounterexample.profile5 =
        pluralityWithRunoff PluralityWithRunoffNegativeInvolvementCounterexample.profile5 := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide)
        (P := PluralityWithRunoffNegativeInvolvementCounterexample.profile5))
  have hIRV6 :
      instantRunoffVoting PluralityWithRunoffNegativeInvolvementCounterexample.profile6 =
        pluralityWithRunoff PluralityWithRunoffNegativeInvolvementCounterexample.profile6 := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide)
        (P := PluralityWithRunoffNegativeInvolvementCounterexample.profile6))
  have hnotmem : (1 : Fin 3) ∉
      instantRunoffVoting PluralityWithRunoffNegativeInvolvementCounterexample.profile5 := by
    have hnotmem' :
        (1 : Fin 3) ∉
          pluralityWithRunoff PluralityWithRunoffNegativeInvolvementCounterexample.profile5 :=
      PluralityWithRunoffNegativeInvolvementCounterexample.pluralityWithRunoff_profile5_not_1
    simpa [hIRV5] using hnotmem'
  have hbottom :
      BallotBottom
        (PluralityWithRunoffNegativeInvolvementCounterexample.profile6.pref
          (newVoter (u := (0 : Fin 6))
            (V := PluralityWithRunoffNegativeInvolvementCounterexample.voters5)
            PluralityWithRunoffNegativeInvolvementCounterexample.voters5_not_mem))
        (1 : Fin 3) :=
    PluralityWithRunoffNegativeInvolvementCounterexample.newVoter_bottom_1
  have hmem : (1 : Fin 3) ∈
      instantRunoffVoting PluralityWithRunoffNegativeInvolvementCounterexample.profile6 := by
    have hmem' :
        (1 : Fin 3) ∈
          pluralityWithRunoff PluralityWithRunoffNegativeInvolvementCounterexample.profile6 :=
      PluralityWithRunoffNegativeInvolvementCounterexample.pluralityWithRunoff_profile6_has_1
    simpa [hIRV6] using hmem'
  have hcontra :=
    hneg
      (V := PluralityWithRunoffNegativeInvolvementCounterexample.voters5)
      (u := (0 : Fin 6))
      (hu := PluralityWithRunoffNegativeInvolvementCounterexample.voters5_not_mem)
      (P := PluralityWithRunoffNegativeInvolvementCounterexample.profile5)
      (Q := PluralityWithRunoffNegativeInvolvementCounterexample.profile6)
      (c := (1 : Fin 3))
      PluralityWithRunoffNegativeInvolvementCounterexample.profiles_agree
      hnotmem
      hbottom
  exact hcontra hmem

theorem instantRunoffVoting_not_subsetReinforcement :
    ¬ SubsetReinforcement instantRunoffVoting := by
  intro hsub
  have hsubset := hsub (U := Fin 13) (A := Fin 3)
    (V := voters8) (W := voters5) (hdisj := voters8_disjoint_voters5)
    (P := profile8) (Q := profile5) (R := profileAll)
    restrict_profileAll_voters8 restrict_profileAll_voters5
  have hIRV8 :
      instantRunoffVoting profile8 = pluralityWithRunoff profile8 := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := profile8))
  have hIRV5 :
      instantRunoffVoting profile5 = pluralityWithRunoff profile5 := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := profile5))
  have hIRVAll :
      instantRunoffVoting profileAll = pluralityWithRunoff profileAll := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := profileAll))
  have hsubset' :
      pluralityWithRunoff profile8 ∩ pluralityWithRunoff profile5 ⊆
        pluralityWithRunoff profileAll := by
    intro x hx
    have hx' : x ∈ instantRunoffVoting profile8 ∩ instantRunoffVoting profile5 := by
      simpa [hIRV8, hIRV5] using hx
    have hx'' := hsubset hx'
    simpa [hIRVAll] using hx''
  exact pluralityWithRunoff_subsetReinforcement_counterexample_sets hsubset'

end SocialChoice
