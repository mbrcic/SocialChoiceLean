import SocialChoice.Axioms.Strategyproofness

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A]

/-! ## Top Sets -/

/-- A ballot has `X` as a top set if every alternative in `X` is above every alternative
    outside `X`. -/
def BallotTopSet (r : LinearOrder A) (X : Finset A) : Prop :=
  ∀ x y : A, x ∈ X → y ∉ X → r.lt x y

/-- A profile has `X` as a top set if every voter has `X` as a top set on their ballot. -/
def TopSet (P : Profile V A) (X : Finset A) : Prop :=
  ∀ v : V, BallotTopSet (P.pref v) X

/-- Apply a list of ballot updates, left-to-right. -/
noncomputable def updateProfileList (P : Profile V A) : List (V × LinearOrder A) → Profile V A
  | [] => P
  | (v, ballot) :: rest => updateProfileList (updateProfile P v ballot) rest

lemma topSet_updateProfile (P : Profile V A) (v : V) (ballot : LinearOrder A) (X : Finset A)
    (hTop : TopSet P X) (hBallot : BallotTopSet ballot X) :
    TopSet (updateProfile P v ballot) X := by
  classical
  intro u
  by_cases huv : u = v
  · subst u
    simpa [updateProfile]
      using hBallot
  · have h := hTop u
    simpa [updateProfile, huv] using h

lemma topSet_singleton_iff_topRank (P : Profile V A) (c : A) :
    TopSet P {c} ↔ ∀ v : V, TopRank P v c := by
  classical
  constructor
  · intro h v d hd
    have h' := h v c d (by simp) (by simp [hd])
    simpa [Prefers] using h'
  · intro h v x y hx hy
    have hx' : x = c := by simpa using hx
    subst x
    have hy' : y ≠ c := by
      simpa using hy
    exact h v y hy'

/-! ## One-Step Top-Set Preservation -/

/-- If a voter with `X` as a top set can change their ballot so that all new winners lie in `X`,
then under pessimist strategyproofness all original winners already lie in `X`. -/
lemma topSet_subset_of_pessimist_update (f : VotingRule)
    (hf_pess : PessimistStrategyproof f)
    (P : Profile V A) (v : V) (ballot : LinearOrder A) (X : Finset A)
    (hTop : TopSet P X)
    (hsubset : f (updateProfile P v ballot) ⊆ X) :
    f P ⊆ X := by
  classical
  intro x hx
  by_contra hxX
  have hmanip :
      ∃ x' ∈ f P, ∀ y ∈ f (updateProfile P v ballot), Prefers P v y x' := by
    refine ⟨x, hx, ?_⟩
    intro y hy
    have hyX : y ∈ X := hsubset hy
    exact hTop v y x hyX hxX
  exact (hf_pess P v ballot) hmanip

lemma topSet_subset_of_pessimist_updates (f : VotingRule)
    (hf_pess : PessimistStrategyproof f)
    (P : Profile V A) (updates : List (V × LinearOrder A)) (X : Finset A)
    (hTop : TopSet P X)
    (hBallots : ∀ u ∈ updates, BallotTopSet u.2 X)
    (hsubset : f (updateProfileList P updates) ⊆ X) :
    f P ⊆ X := by
  classical
  induction updates generalizing P with
  | nil =>
      simpa [updateProfileList] using hsubset
  | cons u rest ih =>
      rcases u with ⟨v, ballot⟩
      have hBallot : BallotTopSet ballot X := hBallots ⟨v, ballot⟩ (by simp)
      have hTop' : TopSet (updateProfile P v ballot) X :=
        topSet_updateProfile (P := P) (v := v) (ballot := ballot) (X := X) hTop hBallot
      have hBallots' : ∀ u ∈ rest, BallotTopSet u.2 X := by
        intro u hu
        exact hBallots u (by simp [hu])
      have hsubset' : f (updateProfileList (updateProfile P v ballot) rest) ⊆ X := by
        simpa [updateProfileList] using hsubset
      have hsubset1 : f (updateProfile P v ballot) ⊆ X :=
        ih (P := updateProfile P v ballot) hTop' hBallots' hsubset'
      exact topSet_subset_of_pessimist_update (f := f) (hf_pess := hf_pess)
        (P := P) (v := v) (ballot := ballot) (X := X) hTop hsubset1

end SocialChoice
