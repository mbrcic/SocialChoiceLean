import Mathlib.Data.Finset.Basic
import SocialChoice.Profile
import SocialChoice.Rules.Schulze.Path
import SocialChoice.Meta

namespace SocialChoice

noncomputable def schulzeDefeats {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Prop :=
  strongestPath P a b > strongestPath P b a

lemma schulzeDefeats_ne {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {a b : A} (h : schulzeDefeats P a b) : a ≠ b := by
  intro hEq
  subst hEq
  exact (lt_irrefl _ h)

lemma schulzeDefeats_asymm {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {a b : A} (h : schulzeDefeats P a b) :
    ¬ schulzeDefeats P b a := by
  exact (lt_asymm h)

@[scRule]
noncomputable def schulze : VotingRule := by
  intro V A _ _ P
  classical
  exact Finset.univ.filter (fun a => ∀ b, ¬ schulzeDefeats P b a)

end SocialChoice
