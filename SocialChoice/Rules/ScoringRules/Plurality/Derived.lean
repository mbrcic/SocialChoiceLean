import SocialChoice.Axioms.Implications
import SocialChoice.Rules.ScoringRules.Anonymity
import SocialChoice.Rules.ScoringRules.Condorcet
import SocialChoice.Rules.ScoringRules.Derived
import SocialChoice.Rules.ScoringRules.Monotonicity
import SocialChoice.Rules.ScoringRules.Neutrality
import SocialChoice.Rules.ScoringRules.Participation
import SocialChoice.Rules.ScoringRules.Reinforcement
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Independence
import SocialChoice.Rules.ScoringRules.Plurality.Majority

namespace SocialChoice

theorem plurality_independenceOfDominated : IndependenceOfDominated plurality := by
  intro V A _ _ _ _ P c d hpref
  exact plurality_independence_of_dominated_nonempty (P := P) (c := c) (d := d) hpref

theorem plurality_independenceOfUniversallyLeastPreferred :
    IndependenceOfUniversallyLeastPreferred plurality := by
  apply Implies.apply independenceOfDominated_implies_independenceOfUniversallyLeastPreferred
    (f := plurality)
  · exact plurality_isVotingRule
  · exact plurality_independenceOfDominated

theorem plurality_unanimity : Unanimity plurality := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := plurality)
  · exact plurality_isVotingRule
  · exact plurality_majority_criterion

lemma pluralityScore_weaklyDecreasing : weaklyDecreasingScore pluralityScore := by
  intro m r s hrs _ _
  by_cases hr0 : r = 0
  · subst hr0
    by_cases hs0 : s = 0
    · subst hs0
      simp [pluralityScore]
    · simp [pluralityScore, hs0]
  · have hs0 : s ≠ 0 := by
      intro hs0
      subst hs0
      have : r = 0 := Nat.eq_zero_of_le_zero hrs
      exact hr0 this
    simp [pluralityScore, hr0, hs0]

lemma plurality_eq_scoringRule_app {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) :
    plurality P = scoringRule pluralityScore P := by
  simpa using congrArg (fun f => f P) plurality_eq_scoringRule

theorem plurality_anonymous : Anonymity plurality := by
  intro V A _ _ P σ
  simpa [plurality_eq_scoringRule_app] using
    (scoringRule_anonymous (score := pluralityScore) (P := P) (σ := σ))

theorem plurality_neutral : Neutrality plurality := by
  intro V A _ _ P σ
  simpa [plurality_eq_scoringRule_app] using
    (scoringRule_neutral (score := pluralityScore) (P := P) (σ := σ))

theorem plurality_monotonicity : Monotonicity plurality := by
  intro V A _ _ P P' x hx hLift
  have hx' : x ∈ scoringRule pluralityScore P := by
    simpa [plurality_eq_scoringRule_app] using hx
  have h' :=
    (scoringRule_monotonicity (score := pluralityScore) pluralityScore_weaklyDecreasing)
      (P := P) (P' := P') (x := x) hx' hLift
  simpa [plurality_eq_scoringRule_app] using h'

theorem plurality_reinforcement : Reinforcement plurality := by
  intro U A _ _ _ V W hdisj P Q R hRV hRW hnonempty
  have hnonempty' : (scoringRule pluralityScore P ∩ scoringRule pluralityScore Q).Nonempty := by
    simpa [plurality_eq_scoringRule_app] using hnonempty
  have h :=
    (scoringRule_reinforcement (score := pluralityScore))
      (V := V) (W := W) (hdisj := hdisj) (P := P) (Q := Q) (R := R) hRV hRW hnonempty'
  simpa [plurality_eq_scoringRule_app] using h

theorem plurality_subsetReinforcement : SubsetReinforcement plurality := by
  intro U A _ _ _ V W hdisj P Q R hRV hRW x hx
  have hx' : x ∈ scoringRule pluralityScore P ∩ scoringRule pluralityScore Q := by
    simpa [plurality_eq_scoringRule_app] using hx
  have h :=
    (scoringRule_subsetReinforcement (score := pluralityScore))
      (V := V) (W := W) (hdisj := hdisj) (P := P) (Q := Q) (R := R) hRV hRW
  have hx'' := h hx'
  simpa [plurality_eq_scoringRule_app] using hx''

theorem plurality_participation : StrongFishburnParticipation plurality := by
  intro U A _ _ _ V u hu P Q hagree
  have h :=
    (scoringRule_strongFishburnParticipation (score := pluralityScore)
      pluralityScore_weaklyDecreasing)
      (V := V) (u := u) (hu := hu) (P := P) (Q := Q) hagree
  simpa [plurality_eq_scoringRule_app] using h

theorem plurality_not_condorcet : ¬ CondorcetConsistency plurality := by
  intro hcond
  have hcond' : CondorcetConsistency (scoringRule pluralityScore) := by
    intro V A _ _ P c hcw
    have h := hcond (P := P) (c := c) hcw
    simpa [plurality_eq_scoringRule_app] using h
  exact (scoringRule_not_condorcet (score := pluralityScore)) hcond'

end SocialChoice
