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
      (Finset.univ.image (fun c => scoreCandidate P score c)).max' (h.image _)
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
    scoreSet.max' (hA.image _)
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

lemma mem_scoringRule_castCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (score : Nat → Nat → Int) {p q : A → Prop}
    (dp : DecidablePred p) (dq : DecidablePred q)
    (h : p = q) (x : {a : A // p a}) (P : Profile V {a : A // p a}) :
    x ∈ scoringRule score P ↔
      ((cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}) ∈
        scoringRule score (castCandidates (p := p) (q := q) h P)) := by
  classical
  letI : DecidablePred p := dp
  letI : DecidablePred q := dq
  cases h
  cases (Subsingleton.elim dq dp)
  rfl

lemma scoringWinners_nonempty {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (score : Nat → Int) : (scoringWinners P score).Nonempty := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  let scoreSet : Finset Int := (Finset.univ.image (fun c => scoreCandidate P score c))
  have hscoreSet : scoreSet.Nonempty := hA.image (fun c => scoreCandidate P score c)
  let maxScore : Int := scoreSet.max' hscoreSet
  have hmaxmem : maxScore ∈ scoreSet := Finset.max'_mem scoreSet hscoreSet
  rcases Finset.mem_image.mp hmaxmem with ⟨c, _hc, hscore⟩
  refine ⟨c, ?_⟩
  simp [scoringWinners, hA, scoreSet, maxScore, hscore]

theorem scoringRule_isVotingRule (score : Nat → Nat → Int) : IsVotingRule (scoringRule score) := by
  intro V A _ _ _ P
  classical
  simpa [scoringRule] using
    (scoringWinners_nonempty (P := P) (score := fun r => score (Fintype.card A) r))

def weaklyDecreasingScore (score : Nat → Nat → Int) : Prop :=
  ∀ m r s, r ≤ s → r < m → s < m → score m s ≤ score m r

def strictlyDecreasingScore (score : Nat → Nat → Int) : Prop :=
  ∀ m r s, r < s → r < m → s < m → score m s < score m r

lemma strictlyDecreasingScore.to_weakly {score : Nat → Nat → Int}
    (hstrict : strictlyDecreasingScore score) : weaklyDecreasingScore score := by
  intro m r s hrs hrm hsm
  rcases lt_or_eq_of_le hrs with hlt | hEq
  · exact (hstrict m r s hlt hrm hsm).le
  · simp [hEq]

end SocialChoice
