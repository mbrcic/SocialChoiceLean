import SocialChoice.Axioms.Anonymity
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

@[simp] lemma plurality_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) :
    plurality (permuteVoters P σ) = plurality P := by
  classical
  simp [plurality, topCount_permuteVoters]

@[simp] lemma secondPluralitySet_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    [DecidableEq A] (P : Profile V A) (σ : Equiv.Perm V) (S : Finset A) :
    secondPluralitySet (permuteVoters P σ) S = secondPluralitySet P S := by
  classical
  simp [secondPluralitySet, topCount_permuteVoters]

@[simp] lemma pluralityWithRunoffPairs_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    [DecidableEq A] (P : Profile V A) (σ : Equiv.Perm V) :
    pluralityWithRunoffPairs (permuteVoters P σ) = pluralityWithRunoffPairs P := by
  classical
  simp [pluralityWithRunoffPairs, secondPluralitySet_permuteVoters]

theorem plurality_with_runoff_anonymous : Anonymity pluralityWithRunoff := by
  intro V A _ _ P σ
  classical
  by_cases hcard : Fintype.card A ≤ 1
  · simp [pluralityWithRunoff, hcard]
  · simp [pluralityWithRunoff, hcard]

end SocialChoice
