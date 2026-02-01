import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

lemma margin_le_of_unanimous_pref {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c d b : A} (hcd : ∀ v : V, Prefers P v c d) :
    margin P d b ≤ margin P c b := by
  classical
  let SD := Finset.univ.filter (fun v => Prefers P v d b)
  let SC := Finset.univ.filter (fun v => Prefers P v c b)
  let BD := Finset.univ.filter (fun v => Prefers P v b d)
  let BC := Finset.univ.filter (fun v => Prefers P v b c)
  have hsub1 : SD ⊆ SC := by
    intro v hv
    have hv' : Prefers P v d b := (Finset.mem_filter.mp hv).2
    have hcdv : Prefers P v c d := hcd v
    let _ := P.pref v
    have hcb : Prefers P v c b := by
      exact lt_trans hcdv hv'
    exact Finset.mem_filter.mpr ⟨by simp, hcb⟩
  have hsub2 : BC ⊆ BD := by
    intro v hv
    have hv' : Prefers P v b c := (Finset.mem_filter.mp hv).2
    have hcdv : Prefers P v c d := hcd v
    let _ := P.pref v
    have hbd : Prefers P v b d := by
      exact lt_trans hv' hcdv
    exact Finset.mem_filter.mpr ⟨by simp, hbd⟩
  have h1 : (Int.ofNat SD.card) ≤ Int.ofNat SC.card :=
    Int.ofNat_le_ofNat_of_le (Finset.card_le_card hsub1)
  have h2 : (Int.ofNat BC.card) ≤ Int.ofNat BD.card :=
    Int.ofNat_le_ofNat_of_le (Finset.card_le_card hsub2)
  have hsub := sub_le_sub h1 h2
  simpa [margin, SD, SC, BD, BC] using hsub

lemma copelandPairScore2_lt_unanimous {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) {c d : A} (hcd : ∀ v : V, Prefers P v c d) :
    copelandPairScore2 (margin P d c) < copelandPairScore2 (margin P c c) := by
  have hpos : margin_pos P c d :=
    unanimous_margin (P := P) (x := c) (y := d) hcd
  have hpos' : 0 < margin P c d := by
    simpa [margin_pos] using hpos
  have hskew : margin P d c = - margin P c d := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) d c
  have hneg : margin P d c < 0 := by linarith
  have hnotpos : ¬ margin P d c > 0 := not_lt_of_ge (le_of_lt hneg)
  have hne : margin P d c ≠ 0 := ne_of_lt hneg
  have hleft : copelandPairScore2 (margin P d c) = 0 := by
    simp [copelandPairScore2, hnotpos, hne]
  have hright : copelandPairScore2 (margin P c c) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  simp [hleft, hright]

lemma copelandScore2_lt_of_unanimous {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) {c d : A} (hcd : ∀ v : V, Prefers P v c d) :
    copelandScore2 P d < copelandScore2 P c := by
  classical
  refine Finset.sum_lt_sum ?_ ?_
  · intro b hb
    have hmargin : margin P d b ≤ margin P c b :=
      margin_le_of_unanimous_pref (P := P) (c := c) (d := d) (b := b) hcd
    exact copelandPairScore2_mono hmargin
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    exact copelandPairScore2_lt_unanimous (P := P) (c := c) (d := d) hcd

/-- Copeland satisfies Pareto efficiency. -/
theorem copeland_pareto_efficiency : ParetoEfficiency copeland := by
  intro V A _ _ _ P c d hcd hd
  classical
  have hscore_lt : copelandScore2 P d < copelandScore2 P c :=
    copelandScore2_lt_of_unanimous (P := P) (c := c) (d := d) hcd
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
  have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 P a)
  have hmax_eq : copelandMaxScore2 P = Finset.max' scores hScores := by
    simp [copelandMaxScore2, hA, scores]
  have hmem_c : copelandScore2 P c ∈ scores := by
    exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
  have hle_max : copelandScore2 P c ≤ copelandMaxScore2 P := by
    have hle' : copelandScore2 P c ≤ Finset.max' scores hScores :=
      Finset.le_max' _ _ hmem_c
    simpa [hmax_eq] using hle'
  have hscore_lt_max : copelandScore2 P d < copelandMaxScore2 P :=
    lt_of_lt_of_le hscore_lt hle_max
  have hnonempty : Nonempty A := ⟨c⟩
  have hdc_eq : copelandScore2 P d = copelandMaxScore2 P := by
    have : d ∈ Finset.univ.filter (fun a => copelandScore2 P a = copelandMaxScore2 P) := by
      simpa [copeland, hnonempty] using hd
    exact (Finset.mem_filter.mp this).2
  linarith

end SocialChoice
