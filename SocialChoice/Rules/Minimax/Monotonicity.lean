import SocialChoice.Axioms.Monotonicity
import SocialChoice.Margin
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

lemma margin_lemma {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (a b : A) (_ : a ≠ b) :
    (∀ v : V, (Prefers P v a b → Prefers P' v a b) ∧
      (Prefers P' v b a → Prefers P v b a)) →
    margin P a b ≤ margin P' a b := by
  classical
  intro lift
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card ≤
        (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    refine cardinality_lemma (p := fun v => Prefers P v a b)
      (q := fun v => Prefers P' v a b) ?_
    intro v hv
    exact (lift v).1 hv
  have h2 :
      (Finset.univ.filter (fun v => Prefers P' v b a)).card ≤
        (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    refine cardinality_lemma (p := fun v => Prefers P' v b a)
      (q := fun v => Prefers P v b a) ?_
    intro v hv
    exact (lift v).2 hv
  have h1' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    exact Int.ofNat_le_ofNat_of_le h1
  have h2' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P' v b a)).card) ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    exact Int.ofNat_le_ofNat_of_le h2
  have hsub := sub_le_sub h1' h2'
  simpa [margin] using hsub

lemma margin_eq_of_simpleLift {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x a b : A) (ha : a ≠ x) (hb : b ≠ x) :
    simpleLift P' P x → margin P a b = margin P' a b := by
  classical
  intro lift
  rcases lift with ⟨lift1, _⟩
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers P' v a b) ?_
    intro v
    exact lift1 v a b ha hb
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers P' v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers P' v b a) ?_
    intro v
    exact lift1 v b a hb ha
  dsimp [margin]
  simp [h1, h2]

lemma margin_le_of_simpleLift_x {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x a : A} (hLift : simpleLift P' P x) :
    margin P' a x ≤ margin P a x := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [self_margin_zero]
  · have hcond :
        ∀ v : V, (Prefers P' v a x → Prefers P v a x) ∧
          (Prefers P v x a → Prefers P' v x a) := by
      intro v
      exact ⟨(hLift.2 a v).2, (hLift.2 a v).1⟩
    exact margin_lemma (P := P') (P' := P) a x hax hcond

lemma margin_le_of_simpleLift_other {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x y a : A} (hLift : simpleLift P' P x) (hy : y ≠ x) :
    margin P a y ≤ margin P' a y := by
  classical
  by_cases hax : a = x
  · have hxy : x ≠ y := by simpa [eq_comm] using hy
    have hcond :
        ∀ v : V, (Prefers P v x y → Prefers P' v x y) ∧
          (Prefers P' v y x → Prefers P v y x) := by
      intro v
      exact ⟨(hLift.2 y v).1, (hLift.2 y v).2⟩
    have h := margin_lemma (P := P) (P' := P') x y hxy hcond
    simpa [hax] using h
  · have hEq : margin P a y = margin P' a y :=
      margin_eq_of_simpleLift P P' x a y hax hy hLift
    exact le_of_eq hEq

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
  exact margin_le_of_simpleLift_x (P := P) (P' := P') (x := x) (a := b) hLift

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
