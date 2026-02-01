import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Meta

namespace SocialChoice

open Finset

/-- A set is dominating if every member pairwise defeats every non-member. -/
def dominatesSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (S : Finset A) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, ∀ b, b ∉ S → margin_pos P a b

lemma dominatesSet_univ {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) : dominatesSet P (Finset.univ : Finset A) := by
  classical
  refine ⟨Finset.univ_nonempty, ?_⟩
  intro a ha b hb
  exact (False.elim (hb (by simp)))

/-- Dominating sets are nested by inclusion. -/
lemma dominatesSet_nested {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {D E : Finset A}
    (hD : dominatesSet P D) (hE : dominatesSet P E) :
    D ⊆ E ∨ E ⊆ D := by
  classical
  by_contra h
  have hDE : ¬ D ⊆ E := by
    intro hDE
    exact h (Or.inl hDE)
  have hED : ¬ E ⊆ D := by
    intro hED
    exact h (Or.inr hED)
  have hd : ∃ d, d ∈ D ∧ d ∉ E := by
    by_contra h'
    apply hDE
    intro d hdD
    by_contra hdE
    exact h' ⟨d, hdD, hdE⟩
  have he : ∃ e, e ∈ E ∧ e ∉ D := by
    by_contra h'
    apply hED
    intro e heE
    by_contra heD
    exact h' ⟨e, heE, heD⟩
  rcases hd with ⟨d, hdD, hdE⟩
  rcases he with ⟨e, heE, heD⟩
  have hde : margin_pos P d e := hD.2 d hdD e heD
  have hed : margin_pos P e d := hE.2 e heE d hdE
  exact (margin_pos_asymm (P := P) d e hde) hed

noncomputable def dominatingSets {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : Finset (Finset A) := by
  classical
  exact (Finset.univ.powerset).filter (fun S => dominatesSet P S)

lemma dominatingSets_nonempty {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) : (dominatingSets (P := P)).Nonempty := by
  classical
  refine ⟨Finset.univ, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, dominatesSet_univ (P := P)⟩
  simp

/-- Existence of a smallest dominating set. -/
theorem exists_min_dominatesSet {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) :
    ∃ S, dominatesSet P S ∧ ∀ T, dominatesSet P T → S ⊆ T := by
  classical
  let DS : Finset (Finset A) := dominatingSets (P := P)
  have hDS : DS.Nonempty := dominatingSets_nonempty (P := P)
  have himage : (DS.image Finset.card).Nonempty := by
    rcases hDS with ⟨S, hS⟩
    exact ⟨Finset.card S, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
  let m : Nat := (DS.image Finset.card).min' himage
  have hm : m ∈ DS.image Finset.card := Finset.min'_mem _ himage
  rcases Finset.mem_image.mp hm with ⟨S, hS, hmS⟩
  have hSdom : dominatesSet P S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hSdom, ?_⟩
  intro T hTdom
  have hTmem : T ∈ DS := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hTdom⟩
    simp
  have hcardTmem : Finset.card T ∈ DS.image Finset.card :=
    Finset.mem_image.mpr ⟨T, hTmem, rfl⟩
  have hmin_le : m ≤ Finset.card T :=
    Finset.min'_le (s := DS.image Finset.card) (x := Finset.card T) hcardTmem
  have hcardS_le : Finset.card S ≤ Finset.card T := by
    simpa [hmS.symm] using hmin_le
  have hnest : S ⊆ T ∨ T ⊆ S := dominatesSet_nested (P := P) hSdom hTdom
  cases hnest with
  | inl hST =>
      exact hST
  | inr hTS =>
      have hEq : T = S :=
        (Finset.subset_iff_eq_of_card_le (s := T) (t := S) hcardS_le).1 hTS
      simp [hEq]

noncomputable def topCycleSet {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) : Finset A :=
  Classical.choose (exists_min_dominatesSet (P := P))

lemma topCycleSet_dominates {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) : dominatesSet P (topCycleSet (P := P)) := by
  classical
  have h := Classical.choose_spec (exists_min_dominatesSet (P := P))
  simpa [topCycleSet] using h.1

lemma topCycleSet_subset_of_dominates {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) {S : Finset A} (hS : dominatesSet P S) :
    topCycleSet (P := P) ⊆ S := by
  classical
  have h := Classical.choose_spec (exists_min_dominatesSet (P := P))
  simpa [topCycleSet] using h.2 S hS

@[scRule]
noncomputable def topCycle : VotingRule := by
  intro V A _ _ P
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    exact topCycleSet (P := P)
  · exact ∅

theorem topCycle_isVotingRule : IsVotingRule topCycle := by
  intro V A _ _ _ P
  classical
  have hA : Nonempty A := inferInstance
  have hdom : dominatesSet P (topCycleSet (P := P)) := topCycleSet_dominates (P := P)
  have hne : (topCycleSet (P := P)).Nonempty := hdom.1
  simpa [topCycle, hA] using hne

end SocialChoice
