import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import SocialChoice.Rank

namespace SocialChoice

open Finset
open scoped BigOperators

-- Total score for a candidate under a scoring vector.
def scoreCandidate {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) (c : A) : Int :=
  ((Finset.univ : Finset V).sum fun v => score (rank (P.pref v) c))

-- Winners for a given scoring vector.
noncomputable def scoringWinners {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) : Finset A := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int :=
      (Finset.univ.image (fun c => scoreCandidate P score c)).max' (by
        simpa [Finset.Nonempty] using h)
    exact
      (Finset.univ.filter (fun c => scoreCandidate P score c = maxScore))
  · exact ∅

lemma scoringWinners_iff_forall_le {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int) (hA : (Finset.univ : Finset A).Nonempty) (c : A) :
    c ∈ scoringWinners P score ↔
      ∀ d : A, scoreCandidate P score d ≤ scoreCandidate P score c := by
  classical
  let scoreSet : Finset Int :=
    (Finset.univ.image (fun x => scoreCandidate P score x))
  let maxScore : Int :=
    scoreSet.max' (by
      simpa [scoreSet, Finset.Nonempty] using hA.image
        (fun x => scoreCandidate P score x))
  constructor
  · intro hc
    have hc' : scoreCandidate P score c = maxScore := by
      simpa [scoringWinners, hA, scoreSet, maxScore] using hc
    intro d
    have hmem : scoreCandidate P score d ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
    have hle : scoreCandidate P score d ≤ maxScore :=
      Finset.le_max' scoreSet _ hmem
    simpa [hc'] using hle
  · intro hle
    have hscoreSet_nonempty : scoreSet.Nonempty := by
      simpa [scoreSet, Finset.Nonempty] using hA.image
        (fun x => scoreCandidate P score x)
    have hmax_le : maxScore ≤ scoreCandidate P score c := by
      refine (Finset.max'_le_iff scoreSet hscoreSet_nonempty).2 ?_
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨d, _hd, rfl⟩
      exact hle d
    have hle_max : scoreCandidate P score c ≤ maxScore := by
      have hmem : scoreCandidate P score c ∈ scoreSet := by
        exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
      exact Finset.le_max' scoreSet _ hmem
    have hmax_eq : scoreCandidate P score c = maxScore := le_antisymm hle_max hmax_le
    have hc' :
        c ∈ (Finset.univ.filter (fun x => scoreCandidate P score x = maxScore)) := by
      exact Finset.mem_filter.mpr ⟨by simp, hmax_eq⟩
    simpa [scoringWinners, hA, scoreSet, maxScore] using hc'

-- Generic positional scoring rule.
noncomputable def scoringRule (score : Nat → Nat → Int) : VotingRule :=
  fun {V A} _ _ (P : Profile V A) =>
    scoringWinners P (fun r => score (Fintype.card A) r)

def weaklyDecreasingScore (score : Nat → Nat → Int) : Prop :=
  ∀ m r s, r ≤ s → score m s ≤ score m r

def strictlyDecreasingScore (score : Nat → Nat → Int) : Prop :=
  ∀ m r s, r < s → score m s < score m r

end SocialChoice
