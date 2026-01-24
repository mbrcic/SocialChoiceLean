import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

theorem plurality_topsOnly : TopsOnly plurality := by
  intro V A _ _ P₁ P₂ htop
  ext c
  simp [plurality, htop]

end SocialChoice
