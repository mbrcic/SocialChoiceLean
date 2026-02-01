import SocialChoice.Axioms.Participation
import SocialChoice.Margin
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

theorem minimax_positive_involvement : PositiveInvolvement minimax := by
  intro U A _ _ V u hu P Q c hagree hc htop
  classical
  let ballot := Q.pref (newVoter (u := u) (V := V) hu)
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  have hnonempty : Nonempty A := ⟨c⟩
  have hc' :
      c ∈ Finset.univ.filter (fun a : A => maxLoss P a = minimaxScore P) := by
    simpa [minimax, hnonempty] using hc
  have hc_eq : maxLoss P c = minimaxScore P := (Finset.mem_filter.mp hc').2
  have hminP : ∀ y, maxLoss P c ≤ maxLoss P y := by
    intro y
    have hle := minimaxScore_le_of_candidate (P := P) y
    linarith [hc_eq]
  by_cases hpos : 0 < maxLoss P c
  · have hmaxLoss_c : maxLoss Q c ≤ maxLoss P c - 1 := by
      refine maxLoss_le_of_forall_margin_le (P := Q) (a := c) (k := maxLoss P c - 1) ?_
      intro b
      by_cases hb : b = c
      · subst hb
        simp [self_margin_zero]
        linarith
      · have hcb : ballot.lt c b := htop b hb
        have hmargin : margin Q b c = margin P b c - 1 :=
          margin_add_newVoter_eq_of_prefers_rev (u := u) (V := V) hu P Q hagree b c hcb
        have hle : margin P b c ≤ maxLoss P c :=
          margin_le_maxLoss (P := P) (a := c) (b := b)
        linarith [hmargin, hle]
    have hmaxLoss_y : ∀ y, maxLoss P y - 1 ≤ maxLoss Q y := by
      intro y
      have hle1 : maxLoss P y ≤ maxLoss Q y + 1 := by
        refine maxLoss_le_of_forall_margin_le (P := P) (a := y) (k := maxLoss Q y + 1) ?_
        intro b
        have h1 : margin P b y ≤ margin Q b y + 1 :=
          margin_le_add_newVoter (u := u) (V := V) hu P Q hagree b y
        have h2 : margin Q b y ≤ maxLoss Q y :=
          margin_le_maxLoss (P := Q) (a := y) (b := b)
        linarith [h1, h2]
      linarith [hle1]
    have hle' : ∀ y, maxLoss Q c ≤ maxLoss Q y := by
      intro y
      have h2 : maxLoss P c ≤ maxLoss P y := hminP y
      have h3 : maxLoss P y - 1 ≤ maxLoss Q y := hmaxLoss_y y
      linarith [hmaxLoss_c, h2, h3]
    have hle_min : maxLoss Q c ≤ minimaxScore Q := by
      refine le_minimaxScore_of_forall (P := Q) (k := maxLoss Q c) hA ?_
      intro y
      exact hle' y
    have hmin_le : minimaxScore Q ≤ maxLoss Q c :=
      minimaxScore_le_of_candidate (P := Q) c
    have hEq : maxLoss Q c = minimaxScore Q := le_antisymm hle_min hmin_le
    have hc_mem :
        c ∈ Finset.univ.filter (fun a : A => maxLoss Q a = minimaxScore Q) := by
      exact Finset.mem_filter.mpr ⟨by simp, hEq⟩
    simpa [minimax, hnonempty] using hc_mem
  · have hnonneg : (0 : Int) ≤ maxLoss P c := by
      have hle := margin_le_maxLoss (P := P) (a := c) (b := c)
      simpa [self_margin_zero] using hle
    have hzero : maxLoss P c = 0 := by
      have hle : maxLoss P c ≤ 0 := le_of_not_gt hpos
      exact le_antisymm hle hnonneg
    have hmaxLoss_c_le : maxLoss Q c ≤ 0 := by
      refine maxLoss_le_of_forall_margin_le (P := Q) (a := c) (k := 0) ?_
      intro b
      by_cases hb : b = c
      · subst hb
        simp [self_margin_zero]
      · have hcb : ballot.lt c b := htop b hb
        have hmargin : margin Q b c = margin P b c - 1 :=
          margin_add_newVoter_eq_of_prefers_rev (u := u) (V := V) hu P Q hagree b c hcb
        have hle : margin P b c ≤ 0 := by
          have hle' : margin P b c ≤ maxLoss P c :=
            margin_le_maxLoss (P := P) (a := c) (b := b)
          linarith [hzero, hle']
        linarith [hmargin, hle]
    have hmaxLoss_c_ge : (0 : Int) ≤ maxLoss Q c := by
      have hle := margin_le_maxLoss (P := Q) (a := c) (b := c)
      simpa [self_margin_zero] using hle
    have hmaxLoss_c : maxLoss Q c = 0 := le_antisymm hmaxLoss_c_le hmaxLoss_c_ge
    have hle' : ∀ y, maxLoss Q c ≤ maxLoss Q y := by
      intro y
      have hnonneg' : (0 : Int) ≤ maxLoss Q y := by
        have hle := margin_le_maxLoss (P := Q) (a := y) (b := y)
        simpa [self_margin_zero] using hle
      linarith [hmaxLoss_c, hnonneg']
    have hle_min : maxLoss Q c ≤ minimaxScore Q := by
      refine le_minimaxScore_of_forall (P := Q) (k := maxLoss Q c) hA ?_
      intro y
      exact hle' y
    have hmin_le : minimaxScore Q ≤ maxLoss Q c :=
      minimaxScore_le_of_candidate (P := Q) c
    have hEq : maxLoss Q c = minimaxScore Q := le_antisymm hle_min hmin_le
    have hc_mem :
        c ∈ Finset.univ.filter (fun a : A => maxLoss Q a = minimaxScore Q) := by
      exact Finset.mem_filter.mpr ⟨by simp, hEq⟩
    simpa [minimax, hnonempty] using hc_mem

end SocialChoice
