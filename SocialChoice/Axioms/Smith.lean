import SocialChoice.Meta
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

/-- Smith criterion: the rule refines TopCycle (Smith set). -/
@[scAxiom]
def SmithCriterion (f : VotingRule) : Prop :=
  Refines f topCycle

theorem smithCriterion_preservedUnderRefinement :
    PreservedUnderRefinement SmithCriterion := by
  intro f g _ _ hfg hSmith
  exact Refines.trans hfg hSmith

end SocialChoice
