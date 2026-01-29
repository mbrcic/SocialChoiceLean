import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Condorcet
import SocialChoice.DebordMcGarvey
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

/-- Majority-margin matrix for a 4-candidate minimax counterexample. -/
abbrev minimaxCondorcetLoserMargins : Fin 4 → Fin 4 → Int := fun a b =>
  match a.1, b.1 with
  | 0, 0 => 0
  | 0, 1 => -3
  | 0, 2 => 3
  | 0, 3 => 1
  | 1, 0 => 3
  | 1, 1 => 0
  | 1, 2 => -3
  | 1, 3 => 1
  | 2, 0 => -3
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 0 => -1
  | 3, 1 => -1
  | 3, 2 => -1
  | 3, 3 => 0
  | _, _ => 0

lemma minimaxCondorcetLoserMargins_skew :
    skew_symmetric minimaxCondorcetLoserMargins := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [minimaxCondorcetLoserMargins]

lemma minimaxCondorcetLoserMargins_odd :
    ∀ a b, a ≠ b → Odd (minimaxCondorcetLoserMargins a b) := by
  intro a b hne
  have h1 : Odd (1 : Int) := by
    exact (odd_one : Odd (1 : Int))
  have h3 : Odd (3 : Int) := by
    simpa using (odd_add_one_self (a := (1 : Int)))
  have hneg1 : Odd (-1 : Int) := by
    exact (odd_neg_one : Odd (-1 : Int))
  have hneg3 : Odd (-3 : Int) := by
    simpa using (odd_neg (a := (3 : Int))).2 h3
  fin_cases a <;> fin_cases b <;> try cases hne rfl
  · change Odd (-3 : Int); exact hneg3
  · change Odd (3 : Int); exact h3
  · change Odd (1 : Int); exact h1
  · change Odd (3 : Int); exact h3
  · change Odd (-3 : Int); exact hneg3
  · change Odd (1 : Int); exact h1
  · change Odd (-3 : Int); exact hneg3
  · change Odd (3 : Int); exact h3
  · change Odd (1 : Int); exact h1
  · change Odd (-1 : Int); exact hneg1
  · change Odd (-1 : Int); exact hneg1
  · change Odd (-1 : Int); exact hneg1

theorem minimax_not_condorcetLoser_criterion : ¬ CondorcetLoserCriterion minimax := by
  intro hcrit
  classical
  obtain ⟨m, P, hmargin⟩ :=
    debordMcGarveyOdd (A := Fin 4)
      minimaxCondorcetLoserMargins
      minimaxCondorcetLoserMargins_skew
      minimaxCondorcetLoserMargins_odd
  let d : Fin 4 := 3
  have hA : (Finset.univ : Finset (Fin 4)).Nonempty := Finset.univ_nonempty

  -- d is a Condorcet loser (all others beat it by margin 1).
  have hloser : CondorcetLoser P d := by
    refine (CondorcetLoser_iff_margin_pos (P := P) (c := d)).2 ?_
    refine ⟨?_, ?_⟩
    · intro a hne
      fin_cases a <;> try cases hne rfl
      ·
        have hmargin0 : margin P 0 d = 1 := by
          simp [hmargin, minimaxCondorcetLoserMargins, d]
        simp [margin_pos, hmargin0]
      ·
        have hmargin1 : margin P 1 d = 1 := by
          simp [hmargin, minimaxCondorcetLoserMargins, d]
        simp [margin_pos, hmargin1]
      ·
        have hmargin2 : margin P 2 d = 1 := by
          simp [hmargin, minimaxCondorcetLoserMargins, d]
        simp [margin_pos, hmargin2]
    · exact ⟨0, by decide⟩

  -- Compute maxLoss for d.
  have hmaxLoss_d_le : maxLoss P d ≤ 1 := by
    refine maxLoss_le_of_forall_margin_le (P := P) (a := d) (k := 1) ?_
    intro b
    fin_cases b <;> simp [hmargin, minimaxCondorcetLoserMargins, d]

  have hmaxLoss_d_ge : (1 : Int) ≤ maxLoss P d := by
    have hle := margin_le_maxLoss (P := P) (a := d) (b := 0)
    have hmargin0 : margin P 0 d = 1 := by
      simp [hmargin, minimaxCondorcetLoserMargins, d]
    simpa [hmargin0] using hle

  have hmaxLoss_d : maxLoss P d = 1 :=
    le_antisymm hmaxLoss_d_le hmaxLoss_d_ge

  -- All candidates have maxLoss ≥ 1.
  have hmaxLoss_ge_one : ∀ a : Fin 4, (1 : Int) ≤ maxLoss P a := by
    intro a
    fin_cases a
    ·
      have hle := margin_le_maxLoss (P := P) (a := (0 : Fin 4)) (b := 1)
      have hmargin10 : margin P 1 0 = 3 := by
        simp [hmargin, minimaxCondorcetLoserMargins]
      have hle' : (3 : Int) ≤ maxLoss P 0 := by
        simpa [hmargin10] using hle
      have h1 : (1 : Int) ≤ (3 : Int) := by decide
      exact le_trans h1 hle'
    ·
      have hle := margin_le_maxLoss (P := P) (a := (1 : Fin 4)) (b := 2)
      have hmargin21 : margin P 2 1 = 3 := by
        simp [hmargin, minimaxCondorcetLoserMargins]
      have hle' : (3 : Int) ≤ maxLoss P 1 := by
        simpa [hmargin21] using hle
      have h1 : (1 : Int) ≤ (3 : Int) := by decide
      exact le_trans h1 hle'
    ·
      have hle := margin_le_maxLoss (P := P) (a := (2 : Fin 4)) (b := 0)
      have hmargin02 : margin P 0 2 = 3 := by
        simp [hmargin, minimaxCondorcetLoserMargins]
      have hle' : (3 : Int) ≤ maxLoss P 2 := by
        simpa [hmargin02] using hle
      have h1 : (1 : Int) ≤ (3 : Int) := by decide
      exact le_trans h1 hle'
    ·
      have hle := margin_le_maxLoss (P := P) (a := (3 : Fin 4)) (b := 0)
      have hmargin03 : margin P 0 3 = 1 := by
        simp [hmargin, minimaxCondorcetLoserMargins]
      simpa [hmargin03] using hle

  -- Compute minimaxScore = 1.
  have hminScore_ge : (1 : Int) ≤ minimaxScore P := by
    exact le_minimaxScore_of_forall (P := P) (k := 1) hA hmaxLoss_ge_one

  have hminScore_le : minimaxScore P ≤ 1 := by
    have hle := minimaxScore_le_of_candidate (P := P) (a := d)
    simpa [hmaxLoss_d] using hle

  have hminScore : minimaxScore P = 1 :=
    le_antisymm hminScore_le hminScore_ge

  have hwin : d ∈ minimax P := by
    classical
    have hmem :
        d ∈ Finset.univ.filter (fun a : Fin 4 => maxLoss P a = minimaxScore P) := by
      simp [hmaxLoss_d, hminScore]
    have hnonempty : Nonempty (Fin 4) := inferInstance
    simpa [minimax, hnonempty] using hmem

  exact (hcrit (P := P) (c := d) hloser) hwin

end SocialChoice
