import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.Defs
import SocialChoice.Meta

namespace SocialChoice

@[scRule]
noncomputable def black : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    by_cases h : ∃ x, CondorcetWinner P x
    · exact {Classical.choose h}
    · exact borda P

end SocialChoice

