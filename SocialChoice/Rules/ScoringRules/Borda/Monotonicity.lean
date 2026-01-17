import SocialChoice.Axioms.Monotonicity
import SocialChoice.Rules.ScoringRules.Borda.Defs
import SocialChoice.Rules.ScoringRules.Monotonicity

namespace SocialChoice

theorem borda_monotonicity : Monotonicity borda := by
  intro V A _ _ P P' x hx hLift
  classical
  have hweak : weaklyDecreasingScore bordaScore :=
    strictlyDecreasingScore.to_weakly bordaScore_strictlyDecreasing
  have hmono :=
    scoringRule_monotonicity (V := V) (A := A) (score := bordaScore) hweak
      (P := P) (P' := P') (x := x) hx hLift
  simpa [borda, scoringRule] using hmono

end SocialChoice
