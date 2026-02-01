import Mathlib.Data.List.Rotate
import Mathlib.Data.List.TakeDrop
import SocialChoice.Axioms.Smith
import SocialChoice.Cycles
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

lemma rotate'_eq_cons_of_mem {A : Type} [DecidableEq A]
    {l : List A} {a : A} (ha : a ∈ l) :
    ∃ t, l.rotate' (List.idxOf a l) = a :: t := by
  classical
  have hlt : List.idxOf a l < l.length := (List.idxOf_lt_length_iff).2 ha
  have hle : List.idxOf a l ≤ l.length := Nat.le_of_lt hlt
  have hrotate :
      l.rotate' (List.idxOf a l) =
        l.drop (List.idxOf a l) ++ l.take (List.idxOf a l) :=
    List.rotate'_eq_drop_append_take hle
  have hdrop :
      l.drop (List.idxOf a l) =
        l[List.idxOf a l] :: l.drop (List.idxOf a l + 1) := by
    simpa using
      (List.cons_getElem_drop_succ (l := l) (n := List.idxOf a l) (h := hlt)).symm
  have hget : l[List.idxOf a l] = a := by
    simp [List.getElem_idxOf (x := a) (xs := l) hlt]
  refine ⟨l.drop (List.idxOf a l + 1) ++ l.take (List.idxOf a l), ?_⟩
  calc
    l.rotate' (List.idxOf a l)
        = l.drop (List.idxOf a l) ++ l.take (List.idxOf a l) := hrotate
    _ = (l[List.idxOf a l] :: l.drop (List.idxOf a l + 1)) ++ l.take (List.idxOf a l) := by
        simp [hdrop]
    _ = a :: (l.drop (List.idxOf a l + 1) ++ l.take (List.idxOf a l)) := by
        simp [hget, List.cons_append]

lemma all_outside_of_chain_cons {A : Type} {R : A → A → Prop} {D : Finset A}
    {x : A} {l : List A}
    (hchain : List.IsChain R (x :: l)) (hx : x ∉ D)
    (hno : ∀ u v, u ∉ D → v ∈ D → ¬ R u v) :
    ∀ z ∈ l, z ∉ D := by
  revert x hchain hx
  induction l with
  | nil =>
      intro x hchain hx z hz
      cases hz
  | cons y t ih =>
      intro x hchain hx z hz
      have hrel : R x y := List.rel_of_isChain_cons_cons hchain
      have hy : y ∉ D := by
        by_contra hyD
        exact (hno x y hx hyD) hrel
      have hchain' : List.IsChain R (y :: t) := List.IsChain.of_cons hchain
      have hz' : z = y ∨ z ∈ t := by
        simpa using hz
      cases hz' with
      | inl hEq =>
          subst hEq
          exact hy
      | inr hzt =>
          exact ih (x := y) hchain' hy _ hzt

lemma splitCycleDefeats_of_dominatesSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {D : Finset A} (hD : dominatesSet P D)
    {a b : A} (ha : a ∈ D) (hb : b ∉ D) :
    splitCycleDefeats P a b := by
  classical
  have hpos_ab : margin_pos P a b := hD.2 a ha b hb
  refine ⟨hpos_ab, ?_⟩
  intro hcyc
  rcases hcyc with ⟨l, haL, hbL, hcycle⟩
  have hno : ∀ u v, u ∉ D → v ∈ D → ¬ (margin P a b ≤ margin P u v) := by
    intro u v hu hv hle
    have hpos_ab' : 0 < margin P a b := by
      simpa [margin_pos] using hpos_ab
    have hpos_uv : 0 < margin P u v := lt_of_lt_of_le hpos_ab' hle
    have hpos_uv' : margin_pos P u v := by
      simpa [margin_pos] using hpos_uv
    have hpos_vu : margin_pos P v u := hD.2 v hv u hu
    exact (margin_pos_asymm (P := P) v u hpos_vu) hpos_uv'
  rcases rotate'_eq_cons_of_mem (a := b) (l := l) hbL with ⟨t, hrot⟩
  let l' : List A := l.rotate' (List.idxOf b l)
  have hcycle' : cycle (fun u v => margin P a b ≤ margin P u v) l' := by
    simpa [l'] using (rotate'_cycle_of_cycle (c := l) (n := List.idxOf b l) hcycle)
  rcases hcycle' with ⟨hne', hchain'⟩
  have hchain_l' : List.IsChain (fun u v => margin P a b ≤ margin P u v) l' :=
    List.IsChain.tail hchain'
  have hchain_cons : List.IsChain (fun u v => margin P a b ≤ margin P u v) (b :: t) := by
    simpa [l', hrot] using hchain_l'
  have hall : ∀ z ∈ t, z ∉ D := all_outside_of_chain_cons hchain_cons hb hno
  have haL' : a ∈ l' := by
    have : a ∈ l.rotate (List.idxOf b l) := (List.mem_rotate).2 haL
    simpa [l', List.rotate_eq_rotate'] using this
  have hab : a ≠ b := by
    intro hEq
    subst hEq
    exact hb ha
  have ha_in_t : a ∈ t := by
    have : a = b ∨ a ∈ t := by
      simpa [l', hrot] using haL'
    cases this with
    | inl hEq => exact (hab hEq).elim
    | inr ht => exact ht
  exact (hall a ha_in_t) ha

/-- Split Cycle satisfies the Smith criterion. -/
theorem splitCycle_smithCriterion : SmithCriterion splitCycle := by
  intro V A _ _ P
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    intro x hx
    have hxcond : ∀ y, ¬ splitCycleDefeats P y x := (Finset.mem_filter.mp hx).2
    by_contra hxD
    have hdom : dominatesSet P (topCycleSet (P := P)) := topCycleSet_dominates (P := P)
    rcases hdom.1 with ⟨y, hy⟩
    have hdef : splitCycleDefeats P y x :=
      splitCycleDefeats_of_dominatesSet (P := P) (D := topCycleSet (P := P)) hdom hy
        (by simpa [topCycle, hA] using hxD)
    exact (hxcond y) hdef
  · intro x hx
    exact (False.elim (hA ⟨x⟩))

end SocialChoice
