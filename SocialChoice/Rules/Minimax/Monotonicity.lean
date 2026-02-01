import SocialChoice.Axioms.Monotonicity
import SocialChoice.Margin
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

lemma maxLoss_le_of_forall_margin {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (a : A)
    (h : ∀ b, margin P b a ≤ margin P' b a) :
    maxLoss P a ≤ maxLoss P' a := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨a, by simp⟩
  set losses : Finset Int := Finset.univ.image (fun b : A => margin P b a)
  set losses' : Finset Int := Finset.univ.image (fun b : A => margin P' b a)
  have hLosses : losses.Nonempty := by
    rcases hA with ⟨b, hb⟩
    exact ⟨margin P b a, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  have hLosses' : losses'.Nonempty := by
    rcases hA with ⟨b, hb⟩
    exact ⟨margin P' b a, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
  have hdef : maxLoss P a = Finset.max' losses hLosses := by
    simp [maxLoss, hA, losses]
  have hdef' : maxLoss P' a = Finset.max' losses' hLosses' := by
    simp [maxLoss, hA, losses']
  have hle :
      Finset.max' losses hLosses ≤ Finset.max' losses' hLosses' := by
    refine
        (Finset.max'_le_iff (s := losses) (H := hLosses)
              (x := Finset.max' losses' hLosses')).2 ?_
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨b, _hb, rfl⟩
    have hmargin : margin P b a ≤ margin P' b a := h b
    have hmem' : margin P' b a ∈ losses' := by
      exact Finset.mem_image.mpr ⟨b, by simp, rfl⟩
    have hle' : margin P' b a ≤ Finset.max' losses' hLosses' :=
      Finset.le_max' _ _ hmem'
    exact le_trans hmargin hle'
  simpa [hdef, hdef'] using hle

lemma maxLoss_le_of_simpleLift_x {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x : A} (hLift : simpleLift P' P x) :
    maxLoss P' x ≤ maxLoss P x := by
  refine maxLoss_le_of_forall_margin (P := P') (P' := P) (a := x) ?_
  intro b
  exact margin_le_of_simpleLift_ax (P := P) (P' := P') (x := x) (a := b) hLift

lemma maxLoss_le_of_simpleLift_other {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x y : A} (hLift : simpleLift P' P x) (hy : y ≠ x) :
    maxLoss P y ≤ maxLoss P' y := by
  refine maxLoss_le_of_forall_margin (P := P) (P' := P') (a := y) ?_
  intro b
  exact margin_le_of_simpleLift_other (P := P) (P' := P') (x := x) (y := y) (a := b) hLift hy

theorem minimax_monotonicity : Monotonicity minimax := by
  intro V A _ _ P P' x hx hLift
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨x, by simp⟩
  have hnonempty : Nonempty A := ⟨x⟩
  have hx' :
      x ∈ Finset.univ.filter (fun a : A => maxLoss P a = minimaxScore P) := by
    simpa [minimax, hnonempty] using hx
  have hx_eq : maxLoss P x = minimaxScore P := (Finset.mem_filter.mp hx').2
  set scores : Finset Int := Finset.univ.image (fun a : A => maxLoss P a)
  have hScores : scores.Nonempty := by
    exact ⟨maxLoss P x, Finset.mem_image.mpr ⟨x, by simp, rfl⟩⟩
  have hdef : minimaxScore P = Finset.min' scores hScores := by
    simp [minimaxScore, hA, scores]
  have hx_eq' : Finset.min' scores hScores = maxLoss P x := by
    calc
      Finset.min' scores hScores = minimaxScore P := by symm; exact hdef
      _ = maxLoss P x := by symm; exact hx_eq
  have hminP : ∀ y, maxLoss P x ≤ maxLoss P y := by
    intro y
    have hmin_prop :=
      (Finset.min'_eq_iff (s := scores) (H := hScores)
            (a := maxLoss P x)).1 hx_eq'
    have hle_all : ∀ b ∈ scores, maxLoss P x ≤ b := hmin_prop.2
    have hmem : maxLoss P y ∈ scores := by
      exact Finset.mem_image.mpr ⟨y, by simp, rfl⟩
    exact hle_all _ hmem
  have hmaxLoss_x : maxLoss P' x ≤ maxLoss P x :=
    maxLoss_le_of_simpleLift_x (P := P) (P' := P') (x := x) hLift
  have hmaxLoss_y : ∀ y, y ≠ x → maxLoss P y ≤ maxLoss P' y := by
    intro y hy
    exact maxLoss_le_of_simpleLift_other (P := P) (P' := P') (x := x) (y := y) hLift hy
  have hle' : ∀ y, maxLoss P' x ≤ maxLoss P' y := by
    intro y
    by_cases hy : y = x
    · subst hy
      exact le_rfl
    · have h1 : maxLoss P' x ≤ maxLoss P x := hmaxLoss_x
      have h2 : maxLoss P x ≤ maxLoss P y := hminP y
      have h3 : maxLoss P y ≤ maxLoss P' y := hmaxLoss_y y hy
      exact le_trans h1 (le_trans h2 h3)
  set scores' : Finset Int := Finset.univ.image (fun a : A => maxLoss P' a)
  have hScores' : scores'.Nonempty := by
    exact ⟨maxLoss P' x, Finset.mem_image.mpr ⟨x, by simp, rfl⟩⟩
  have hdef' : minimaxScore P' = Finset.min' scores' hScores' := by
    simp [minimaxScore, hA, scores']
  have hle_min : maxLoss P' x ≤ minimaxScore P' := by
    have hle : ∀ y ∈ scores', maxLoss P' x ≤ y := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨y, _hy, rfl⟩
      exact hle' y
    simpa [hdef'] using (Finset.le_min' (s := scores') (H := hScores') (x := maxLoss P' x) hle)
  have hmin_le : minimaxScore P' ≤ maxLoss P' x := by
    have hmem : maxLoss P' x ∈ scores' := by
      exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
    simpa [hdef'] using (Finset.min'_le (s := scores') (H2 := hmem))
  have hx_eq' : maxLoss P' x = minimaxScore P' := le_antisymm hle_min hmin_le
  have hx_mem :
      x ∈ Finset.univ.filter (fun a : A => maxLoss P' a = minimaxScore P') := by
    exact Finset.mem_filter.mpr ⟨by simp, hx_eq'⟩
  simpa [minimax, hnonempty] using hx_mem

end SocialChoice
