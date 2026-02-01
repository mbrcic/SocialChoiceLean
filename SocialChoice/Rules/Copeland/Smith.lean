import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SocialChoice.Axioms.Smith
import SocialChoice.Rules.Copeland.Defs
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

lemma copelandScore2_lt_of_not_mem_dominatesSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {D : Finset A} (hD : dominatesSet P D)
    {d : A} (hd : d ∈ D) {e : A} (he : e ∉ D) :
    copelandScore2 P e < copelandScore2 P d := by
  classical
  have hpos_de : margin_pos P d e := hD.2 d hd e he
  have hle : ∀ b, b ∈ (Finset.univ : Finset A) →
      copelandPairScore2 (margin P e b) ≤ copelandPairScore2 (margin P d b) := by
    intro b hb
    by_cases hbD : b ∈ D
    · have hpos_be : margin_pos P b e := hD.2 b hbD e he
      have hskew : margin P e b = - margin P b e := by
        simpa [skew_symmetric] using (margin_antisymmetric (P := P)) e b
      have hpos' : margin P b e > 0 := by
        simpa [margin_pos] using hpos_be
      have hneg : margin P e b < 0 := by
        linarith
      have hscore_e : copelandPairScore2 (margin P e b) = 0 := by
        have hpos'' : ¬ margin P e b > 0 := not_lt_of_ge (le_of_lt hneg)
        have hzero'' : margin P e b ≠ 0 := ne_of_lt hneg
        simp [copelandPairScore2, hpos'', hzero'']
      have hscore_d : 0 ≤ copelandPairScore2 (margin P d b) :=
        copelandPairScore2_nonneg _
      simpa [hscore_e] using hscore_d
    · have hpos_db : margin_pos P d b := hD.2 d hd b hbD
      have hpos' : margin P d b > 0 := by
        simpa [margin_pos] using hpos_db
      have hscore_d : copelandPairScore2 (margin P d b) = 2 := by
        simp [copelandPairScore2, hpos']
      have hscore_e : copelandPairScore2 (margin P e b) ≤ 2 :=
        copelandPairScore2_le_two _
      simpa [hscore_d] using hscore_e
  have hlt : ∃ b, b ∈ (Finset.univ : Finset A) ∧
      copelandPairScore2 (margin P e b) < copelandPairScore2 (margin P d b) := by
    have hskew : margin P e d = - margin P d e := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P)) e d
    have hpos' : margin P d e > 0 := by
      simpa [margin_pos] using hpos_de
    have hneg : margin P e d < 0 := by
      linarith
    have hscore_e : copelandPairScore2 (margin P e d) = 0 := by
      have hpos'' : ¬ margin P e d > 0 := not_lt_of_ge (le_of_lt hneg)
      have hzero'' : margin P e d ≠ 0 := ne_of_lt hneg
      simp [copelandPairScore2, hpos'', hzero'']
    have hscore_d : copelandPairScore2 (margin P d d) = 1 := by
      simp [copelandPairScore2, self_margin_zero]
    refine ⟨d, by simp, ?_⟩
    simp [hscore_e, hscore_d]
  simpa [copelandScore2] using (Finset.sum_lt_sum hle hlt)

lemma copeland_subset_of_dominatesSet {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) {D : Finset A} (hD : dominatesSet P D) :
    copeland P ⊆ D := by
  classical
  intro x hx
  by_contra hxD
  rcases hD.1 with ⟨d, hdD⟩
  have hlt : copelandScore2 P x < copelandScore2 P d :=
    copelandScore2_lt_of_not_mem_dominatesSet (P := P) (D := D) hD hdD hxD
  have hA : Nonempty A := inferInstance
  have hxscore : copelandScore2 P x = copelandMaxScore2 (V := V) (A := A) P := by
    have hx' : x ∈
        Finset.univ.filter (fun a => copelandScore2 P a = copelandMaxScore2 (V := V) (A := A) P) := by
      simpa [copeland, hA] using hx
    exact (Finset.mem_filter.mp hx').2
  have hAuniv : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  have hmem_scores :
      copelandScore2 P d ∈ (Finset.univ.image (fun a => copelandScore2 P a)) := by
    exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
  have hle' : copelandScore2 P d ≤ copelandMaxScore2 (V := V) (A := A) P := by
    have hle'' : copelandScore2 P d ≤
        Finset.max'
          (Finset.univ.image (fun a => copelandScore2 P a))
          (hAuniv.image (fun a => copelandScore2 P a)) :=
      Finset.le_max' _ _ hmem_scores
    simpa [copelandMaxScore2, hAuniv] using hle''
  have hle : copelandScore2 P d ≤ copelandScore2 P x := by
    simpa [hxscore] using hle'
  exact (not_lt_of_ge hle hlt)

/-- Copeland satisfies the Smith criterion. -/
theorem copeland_smithCriterion : SmithCriterion copeland := by
  intro V A _ _ P
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    have hsubset : copeland P ⊆ topCycleSet (P := P) :=
      copeland_subset_of_dominatesSet (P := P)
        (D := topCycleSet (P := P)) (topCycleSet_dominates (P := P))
    simpa [topCycle, hA] using hsubset
  · simp [copeland, topCycle, hA]

end SocialChoice
