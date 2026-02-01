import SocialChoice.Axioms.Condorcet
import SocialChoice.Margin
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

lemma copelandScore2_condorcetLoser_eq_one {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hloser : CondorcetLoser P c) :
    copelandScore2 P c = 1 := by
  classical
  have hpos : ∀ b, b ≠ c → margin_pos P b c := by
    intro b hb
    exact (CondorcetLoser_iff_margin_pos P c).1 hloser |>.1 b (by simpa [eq_comm] using hb)
  have hscore_other : ∀ b, b ≠ c → copelandPairScore2 (margin P c b) = 0 := by
    intro b hb
    have hpos' : 0 < margin P b c := by
      simpa [margin_pos] using hpos b hb
    have hskew : margin P c b = - margin P b c := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P)) c b
    have hneg : margin P c b < 0 := by linarith
    have hnotpos : ¬ margin P c b > 0 := not_lt_of_ge (le_of_lt hneg)
    have hne : margin P c b ≠ 0 := ne_of_lt hneg
    simp [copelandPairScore2, hnotpos, hne]
  have hscore_self : copelandPairScore2 (margin P c c) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have hsum :
      Finset.sum (s := (Finset.univ : Finset A))
        (fun b => copelandPairScore2 (margin P c b)) =
        copelandPairScore2 (margin P c c) := by
    apply Finset.sum_eq_single_of_mem c (by simp)
    intro b hb hbc
    exact hscore_other b hbc
  simp [copelandScore2, hsum, hscore_self]

lemma copelandScore2_ge_three_of_beats {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c d : A} (hcd : d ≠ c) (hpos : margin_pos P d c) :
    (3 : Int) ≤ copelandScore2 P d := by
  classical
  have hsubset : ({c, d} : Finset A) ⊆ (Finset.univ : Finset A) := by
    intro x hx
    simp
  have hnonneg : ∀ b ∈ (Finset.univ : Finset A), b ∉ ({c, d} : Finset A) →
      0 ≤ copelandPairScore2 (margin P d b) := by
    intro b hb hnot
    exact copelandPairScore2_nonneg (margin P d b)
  have hsum_le :
      Finset.sum (s := ({c, d} : Finset A))
        (fun b => copelandPairScore2 (margin P d b)) ≤
        Finset.sum (s := (Finset.univ : Finset A))
          (fun b => copelandPairScore2 (margin P d b)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hpair :
      Finset.sum (s := ({c, d} : Finset A))
        (fun b => copelandPairScore2 (margin P d b)) =
        copelandPairScore2 (margin P d c) + copelandPairScore2 (margin P d d) := by
    have hdc : c ≠ d := by simpa [eq_comm] using hcd
    simp [Finset.sum_pair hdc]
  have hscore_dc : copelandPairScore2 (margin P d c) = 2 := by
    have hpos' : margin P d c > 0 := by simpa [margin_pos] using hpos
    simp [copelandPairScore2, hpos']
  have hscore_dd : copelandPairScore2 (margin P d d) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have hsum_pair :
      Finset.sum (s := ({c, d} : Finset A))
        (fun b => copelandPairScore2 (margin P d b)) = 3 := by
    simp [hpair, hscore_dc, hscore_dd]
  have hle :
      Finset.sum (s := ({c, d} : Finset A))
        (fun b => copelandPairScore2 (margin P d b)) ≤
        copelandScore2 P d := by
    simpa [copelandScore2] using hsum_le
  simpa [hsum_pair] using hle

/-- Copeland satisfies the Condorcet loser criterion. -/
theorem copeland_CondorcetLoser_criterion : CondorcetLoserCriterion copeland := by
  intro V A _ _ P c hloser
  classical
  rcases hloser.2 with ⟨d, hdc⟩
  have hnonempty : Nonempty A := ⟨d⟩
  have hpos : margin_pos P d c :=
    (CondorcetLoser_iff_margin_pos P c).1 hloser |>.1 d (by simpa [eq_comm] using hdc)
  have hscore_c : copelandScore2 P c = 1 :=
    copelandScore2_condorcetLoser_eq_one (P := P) hloser
  have hscore_d : (3 : Int) ≤ copelandScore2 P d :=
    copelandScore2_ge_three_of_beats (P := P) (hcd := hdc) hpos
  have hscore_lt : copelandScore2 P c < copelandScore2 P d := by
    linarith

  -- Show that c cannot be a max-score winner.
  have hA : (Finset.univ : Finset A).Nonempty := ⟨d, by simp⟩
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
  have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 P a)
  have hmax_eq : copelandMaxScore2 P = Finset.max' scores hScores := by
    simp [copelandMaxScore2, hA, scores]
  have hmem_d : copelandScore2 P d ∈ scores := by
    exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
  have hle_max : copelandScore2 P d ≤ copelandMaxScore2 P := by
    have hle' : copelandScore2 P d ≤ Finset.max' scores hScores :=
      Finset.le_max' _ _ hmem_d
    simpa [hmax_eq] using hle'
  have hscore_c_lt_max : copelandScore2 P c < copelandMaxScore2 P :=
    lt_of_lt_of_le hscore_lt hle_max

  intro hc
  have hc' : copelandScore2 P c = copelandMaxScore2 P := by
    have : c ∈ Finset.univ.filter (fun a => copelandScore2 P a = copelandMaxScore2 P) := by
      simpa [copeland, hnonempty] using hc
    exact (Finset.mem_filter.mp this).2
  linarith

end SocialChoice
