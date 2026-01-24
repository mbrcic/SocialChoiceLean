import SocialChoice.Profile
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset

noncomputable def topCount {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Nat :=
  (votersTop P c).card

@[simp] lemma topCount_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) (c : A) :
    topCount (permuteVoters P σ) c = topCount P c := by
  classical
  have hcard :
      (votersTop (permuteVoters P σ) c).card = (votersTop P c).card := by
    refine Finset.card_bij
      (s := votersTop (permuteVoters P σ) c)
      (t := votersTop P c)
      (i := fun v _ => σ v) ?_ ?_ ?_
    · intro v hv
      have hv' : TopRank (permuteVoters P σ) v c := (Finset.mem_filter.mp hv).2
      have hv'' : TopRank P (σ v) c := by
        intro d hd
        have : Prefers (permuteVoters P σ) v c d := hv' d hd
        simpa [permuteVoters, Prefers] using this
      exact Finset.mem_filter.mpr ⟨by simp, hv''⟩
    · intro v1 hv1 v2 hv2 h
      exact σ.injective h
    · intro v hv
      have hv' : TopRank P v c := (Finset.mem_filter.mp hv).2
      refine ⟨σ.symm v, ?_, by simp⟩
      have : TopRank (permuteVoters P σ) (σ.symm v) c := by
        intro d hd
        have : Prefers P v c d := hv' d hd
        simpa [permuteVoters, Prefers] using this
      exact Finset.mem_filter.mpr ⟨by simp, this⟩
  simpa [topCount] using hcard

-- Concrete rules.
noncomputable def trivialRule : VotingRule :=
  fun {V A} _ _ (_ : Profile V A) => (Finset.univ : Finset A)

end SocialChoice
