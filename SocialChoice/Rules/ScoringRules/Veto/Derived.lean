import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringRules.Anonymity
import SocialChoice.Rules.ScoringRules.Condorcet
import SocialChoice.Rules.ScoringRules.Derived
import SocialChoice.Rules.ScoringRules.Monotonicity
import SocialChoice.Rules.ScoringRules.Neutrality
import SocialChoice.Rules.ScoringRules.Participation
import SocialChoice.Rules.ScoringRules.Reinforcement
import SocialChoice.Rules.ScoringRules.Veto.Defs
import SocialChoice.Rules.ScoringRules.Veto.Unanimity

namespace SocialChoice

lemma vetoScore_weaklyDecreasing : weaklyDecreasingScore vetoScore := by
  intro m r s hrs hrm hsm
  by_cases hr : r = m - 1
  · have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hrm
    have hm : m = Nat.succ (m - 1) := (Nat.succ_pred_eq_of_pos hmpos).symm
    have hs_le : s ≤ m - 1 := by
      have hsm' := hsm
      rw [hm] at hsm'
      exact Nat.lt_succ_iff.mp hsm'
    have hs_ge : m - 1 ≤ s := by simpa [hr] using hrs
    have hs : s = m - 1 := Nat.le_antisymm hs_le hs_ge
    subst hs
    simp [vetoScore, hr]
  · by_cases hs : s = m - 1
    · simp [vetoScore, hr, hs]
    · simp [vetoScore, hr, hs]

theorem veto_anonymous : Anonymity veto := by
  intro V A _ _ P σ
  simpa [veto] using (scoringRule_anonymous (score := vetoScore) (P := P) (σ := σ))

theorem veto_neutral : Neutrality veto := by
  intro V A _ _ P σ
  simpa [veto] using (scoringRule_neutral (score := vetoScore) (P := P) (σ := σ))

theorem veto_monotonicity : Monotonicity veto := by
  intro V A _ _ P P' x hx hLift
  have hx' : x ∈ scoringRule vetoScore P := by
    simpa [veto] using hx
  have h' :=
    (scoringRule_monotonicity (score := vetoScore) vetoScore_weaklyDecreasing)
      (P := P) (P' := P') (x := x) hx' hLift
  simpa [veto] using h'

theorem veto_reinforcement : Reinforcement veto := by
  intro U A _ _ _ V W hdisj P Q R hRV hRW hnonempty
  have hnonempty' : (scoringRule vetoScore P ∩ scoringRule vetoScore Q).Nonempty := by
    simpa [veto] using hnonempty
  have h :=
    (scoringRule_reinforcement (score := vetoScore))
      (V := V) (W := W) (hdisj := hdisj) (P := P) (Q := Q) (R := R) hRV hRW hnonempty'
  simpa [veto] using h

theorem veto_subsetReinforcement : SubsetReinforcement veto := by
  intro U A _ _ _ V W hdisj P Q R hRV hRW x hx
  have hx' : x ∈ scoringRule vetoScore P ∩ scoringRule vetoScore Q := by
    simpa [veto] using hx
  have h :=
    (scoringRule_subsetReinforcement (score := vetoScore))
      (V := V) (W := W) (hdisj := hdisj) (P := P) (Q := Q) (R := R) hRV hRW
  have hx'' := h hx'
  simpa [veto] using hx''

theorem veto_participation : StrongFishburnParticipation veto := by
  intro U A _ _ _ V u hu P Q hagree
  have h :=
    (scoringRule_strongFishburnParticipation (score := vetoScore)
      vetoScore_weaklyDecreasing)
      (V := V) (u := u) (hu := hu) (P := P) (Q := Q) hagree
  simpa [veto] using h

theorem veto_positive_involvement : PositiveInvolvement veto := by
  apply Implies.apply strongFishburnParticipation_implies_positiveInvolvement (f := veto)
  · exact veto_isVotingRule
  · exact veto_participation

theorem veto_negative_involvement : NegativeInvolvement veto := by
  apply Implies.apply strongFishburnParticipation_implies_negativeInvolvement (f := veto)
  · exact veto_isVotingRule
  · exact veto_participation

theorem veto_not_condorcet : ¬ CondorcetConsistency veto := by
  simpa [veto] using (scoringRule_not_condorcet (score := vetoScore))

theorem veto_not_smithCriterion : ¬ SmithCriterion veto := by
  intro hsmith
  have hcond : CondorcetConsistency veto :=
    Implies.apply smithCriterion_implies_condorcetConsistency_Imp
      (f := veto) veto_isVotingRule hsmith
  exact veto_not_condorcet hcond

theorem veto_not_pareto_efficiency : ¬ ParetoEfficiency veto := by
  intro hpareto
  have hunan : Unanimity veto :=
    Implies.apply paretoEfficiency_implies_unanimity (f := veto) veto_isVotingRule hpareto
  exact veto_not_unanimity hunan

theorem veto_not_independenceOfDominated : ¬ IndependenceOfDominated veto := by
  intro hInd
  have hPareto : ParetoEfficiency veto :=
    Implies.apply independenceOfDominated_implies_paretoEfficiency (f := veto)
      veto_isVotingRule hInd
  exact veto_not_pareto_efficiency hPareto

end SocialChoice
