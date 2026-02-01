import SocialChoice.Axioms.Monotonicity
import SocialChoice.Margin
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

lemma copelandScore2_le_of_simpleLift_x {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x : A} (hLift : simpleLift P' P x) :
    copelandScore2 P x ≤ copelandScore2 P' x := by
  classical
  refine Finset.sum_le_sum ?_
  intro b hb
  have hmargin : margin P x b ≤ margin P' x b :=
    margin_le_of_simpleLift_xa (P := P) (P' := P') (x := x) (a := b) hLift
  exact copelandPairScore2_mono hmargin

lemma copelandScore2_le_of_simpleLift_other {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x y : A} (hLift : simpleLift P' P x) (hy : y ≠ x) :
    copelandScore2 P' y ≤ copelandScore2 P y := by
  classical
  refine Finset.sum_le_sum ?_
  intro b hb
  by_cases hb' : b = x
  · have hmargin : margin P' y b ≤ margin P y b := by
      simpa [hb'] using
        (margin_le_of_simpleLift_ax (P := P) (P' := P') (x := x) (a := y) hLift)
    exact copelandPairScore2_mono hmargin
  · have hmargin_eq : margin P y b = margin P' y b :=
      margin_eq_of_simpleLift P P' x y b hy hb' hLift
    simp [hmargin_eq]

/-- Copeland satisfies monotonicity under simple lifts. -/
theorem copeland_monotonicity : Monotonicity copeland := by
  intro V A _ _ P P' x hx hLift
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨x, by simp⟩
  have hnonempty : Nonempty A := ⟨x⟩

  -- x is a max-score winner in P
  have hx' :
      x ∈ Finset.univ.filter (fun a => copelandScore2 P a = copelandMaxScore2 P) := by
    simpa [copeland, hnonempty] using hx
  have hx_eq : copelandScore2 P x = copelandMaxScore2 P :=
    (Finset.mem_filter.mp hx').2

  -- Any score in P is bounded by x's score
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
  have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 P a)
  have hdef : copelandMaxScore2 P = Finset.max' scores hScores := by
    simp [copelandMaxScore2, hA, scores]
  have hx_eq' : copelandScore2 P x = Finset.max' scores hScores := by
    simpa [hdef] using hx_eq
  have hscore_le_x : ∀ y, copelandScore2 P y ≤ copelandScore2 P x := by
    intro y
    have hmem : copelandScore2 P y ∈ scores := by
      exact Finset.mem_image.mpr ⟨y, by simp, rfl⟩
    have hle : copelandScore2 P y ≤ Finset.max' scores hScores :=
      Finset.le_max' _ _ hmem
    simpa [hx_eq'] using hle

  -- x's score does not decrease, others' scores do not increase
  have hscore_x : copelandScore2 P x ≤ copelandScore2 P' x :=
    copelandScore2_le_of_simpleLift_x (P := P) (P' := P') (x := x) hLift
  have hscore_y : ∀ y, y ≠ x → copelandScore2 P' y ≤ copelandScore2 P y := by
    intro y hy
    exact copelandScore2_le_of_simpleLift_other (P := P) (P' := P') (x := x) (y := y) hLift hy

  have hle_all : ∀ y, copelandScore2 P' y ≤ copelandScore2 P' x := by
    intro y
    by_cases hy : y = x
    · subst hy
      exact le_rfl
    · have h1 : copelandScore2 P' y ≤ copelandScore2 P y := hscore_y y hy
      have h2 : copelandScore2 P y ≤ copelandScore2 P x := hscore_le_x y
      exact le_trans h1 (le_trans h2 hscore_x)

  -- Show x attains the max score in P'
  let scores' : Finset Int := Finset.univ.image (fun a => copelandScore2 P' a)
  have hScores' : scores'.Nonempty := hA.image (fun a => copelandScore2 P' a)
  have hdef' : copelandMaxScore2 P' = Finset.max' scores' hScores' := by
    simp [copelandMaxScore2, hA, scores']
  have hmax_le : Finset.max' scores' hScores' ≤ copelandScore2 P' x := by
    refine (Finset.max'_le_iff _ _).2 ?_
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, _hy, rfl⟩
    exact hle_all y
  have hle_max : copelandScore2 P' x ≤ Finset.max' scores' hScores' := by
    have hmem : copelandScore2 P' x ∈ scores' := by
      exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
    exact Finset.le_max' _ _ hmem
  have hmax_eq : copelandMaxScore2 P' = copelandScore2 P' x := by
    have : Finset.max' scores' hScores' = copelandScore2 P' x :=
      le_antisymm hmax_le hle_max
    simpa [hdef'] using this

  have hx_mem :
      x ∈ Finset.univ.filter (fun a => copelandScore2 P' a = copelandMaxScore2 P') := by
    exact Finset.mem_filter.mpr ⟨by simp, by symm; exact hmax_eq⟩
  simpa [copeland, hnonempty] using hx_mem

end SocialChoice
