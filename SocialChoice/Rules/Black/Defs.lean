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

theorem black_isVotingRule : IsVotingRule black := by
  intro V A _ _ _ P
  classical
  by_cases h : ∃ x, CondorcetWinner P x
  · simp [black, h]
  · simpa [black, h] using (borda_isVotingRule (V := V) (A := A) (P := P))

end SocialChoice
