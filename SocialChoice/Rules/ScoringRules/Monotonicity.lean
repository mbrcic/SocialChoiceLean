import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SocialChoice.Axioms.Monotonicity
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset

lemma rank_le_of_simpleLift_x {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x : A} (h : simpleLift P' P x) (v : V) :
    rank (P'.pref v) x ≤ rank (P.pref v) x := by
  classical
  refine Finset.card_le_card ?_
  intro d hd
  have hd' : Prefers P' v d x := (Finset.mem_filter.mp hd).2
  have hd'' : Prefers P v d x := (h.2 d v).2 hd'
  exact Finset.mem_filter.mpr ⟨by simp, hd''⟩

lemma rank_le_of_simpleLift_other {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x y : A} (h : simpleLift P' P x) (hy : y ≠ x) (v : V) :
    rank (P.pref v) y ≤ rank (P'.pref v) y := by
  classical
  refine Finset.card_le_card ?_
  intro d hd
  have hd' : Prefers P v d y := (Finset.mem_filter.mp hd).2
  have hd'' : Prefers P' v d y := by
    by_cases hdx : d = x
    · subst hdx
      exact (h.2 y v).1 hd'
    · have h1 := h.1 v d y hdx hy
      exact (h1.mp hd')
  exact Finset.mem_filter.mpr ⟨by simp, hd''⟩

theorem scoringRule_monotonicity (score : Nat → Nat → Int)
    (hmono : weaklyDecreasingScore score) :
    Monotonicity (scoringRule score) := by
  intro V A _ _ P P' x hx hLift
  classical
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
  have hA : (Finset.univ : Finset A).Nonempty := ⟨x, by simp⟩
  let scoreSet : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate P scoreFun c))
  let maxScore : Int :=
    scoreSet.max' (by
      simpa [scoreSet, Finset.Nonempty] using hA)
  have hx' : x ∈ scoringWinners P scoreFun := by
    simpa [scoringRule, scoreFun] using hx
  have hx_eq : scoreCandidate P scoreFun x = maxScore := by
    simpa [scoringWinners, hA, scoreSet, maxScore] using hx'
  have hPmax : ∀ y, scoreCandidate P scoreFun y ≤ scoreCandidate P scoreFun x := by
    intro y
    have hmem :
        scoreCandidate P scoreFun y ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨y, by simp, rfl⟩
    have hle : scoreCandidate P scoreFun y ≤ maxScore :=
      Finset.le_max' scoreSet _ hmem
    simpa [hx_eq] using hle
  have hscore_x : scoreCandidate P scoreFun x ≤ scoreCandidate P' scoreFun x := by
    unfold scoreCandidate
    refine Finset.sum_le_sum ?_
    intro v hv
    have hrank : rank (P'.pref v) x ≤ rank (P.pref v) x :=
      rank_le_of_simpleLift_x (P := P) (P' := P') (x := x) hLift v
    exact hmono (Fintype.card A) _ _ hrank
  have hscore_y : ∀ y, y ≠ x → scoreCandidate P' scoreFun y ≤ scoreCandidate P scoreFun y := by
    intro y hy
    unfold scoreCandidate
    refine Finset.sum_le_sum ?_
    intro v hv
    have hrank : rank (P.pref v) y ≤ rank (P'.pref v) y :=
      rank_le_of_simpleLift_other (P := P) (P' := P') (x := x) (y := y) hLift hy v
    exact hmono (Fintype.card A) _ _ hrank
  have hle' : ∀ y, scoreCandidate P' scoreFun y ≤ scoreCandidate P' scoreFun x := by
    intro y
    by_cases hy : y = x
    · simpa [hy]
    · have h1 := hscore_y y hy
      have h2 := hPmax y
      have h3 := hscore_x
      exact le_trans h1 (le_trans h2 h3)
  let scoreSet' : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate P' scoreFun c))
  let maxScore' : Int :=
    scoreSet'.max' (by
      simpa [scoreSet', Finset.Nonempty] using hA)
  have hmax_le : maxScore' ≤ scoreCandidate P' scoreFun x := by
    have hscoreSet_nonempty : scoreSet'.Nonempty := by
      simpa [scoreSet', Finset.Nonempty] using hA
    refine (Finset.max'_le_iff scoreSet' hscoreSet_nonempty).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨c, _hc, rfl⟩
    exact hle' c
  have hle_max : scoreCandidate P' scoreFun x ≤ maxScore' := by
    have hmem :
        scoreCandidate P' scoreFun x ∈ scoreSet' := by
      exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
    exact Finset.le_max' scoreSet' _ hmem
  have hmax_eq : scoreCandidate P' scoreFun x = maxScore' :=
    le_antisymm hle_max hmax_le
  have hx'' : x ∈ scoringWinners P' scoreFun := by
    have hxmem : x ∈ (Finset.univ : Finset A) := by simp
    have : x ∈ (Finset.univ.filter
        (fun c => scoreCandidate P' scoreFun c = maxScore')) := by
      exact Finset.mem_filter.mpr ⟨hxmem, hmax_eq⟩
    simpa [scoringWinners, hA, scoreSet', maxScore'] using this
  simpa [scoringRule, scoreFun] using hx''

end SocialChoice
