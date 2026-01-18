import SocialChoice.Axioms.Condorcet
import SocialChoice.Margin
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

/-- Minimax satisfies the Condorcet criterion: if a Condorcet winner exists,
then it is the unique winner returned by the rule. -/
theorem minimax_condorcet_consistency : CondorcetConsistency minimax := by
  intro V A _ _ P c hw
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, Finset.mem_univ c⟩
  have hnonempty : Nonempty A := ⟨c⟩

  -- The Condorcet winner never loses, so its worst loss is 0.
  have hmaxLoss_c_zero : maxLoss P c = 0 := by
    classical
    set losses : Finset Int := Finset.univ.image (fun b : A => margin P b c)
    have hLosses : losses.Nonempty := by
      rcases hA with ⟨b, hb⟩
      exact ⟨margin P b c, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    have hle0 : ∀ x ∈ losses, x ≤ 0 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨b, _, rfl⟩
      by_cases hb : b = c
      · subst hb; simp [margin]
      · have hpos : margin_pos P c b :=
          (CondorcetWinner_iff_margin_pos P c).mp hw b (by simpa [eq_comm] using hb)
        have hskew : margin P b c = - margin P c b := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P)) b c
        have hneg : margin P b c < 0 := by
          have hpos' : 0 < margin P c b := by simpa [margin_pos] using hpos
          linarith
        exact le_of_lt hneg
    have hmax_le_zero : Finset.max' losses hLosses ≤ 0 :=
      (Finset.max'_le_iff _ _).2 hle0
    have hzero_le_max : 0 ≤ Finset.max' losses hLosses := by
      have hmem0 : 0 ∈ losses := by
        refine Finset.mem_image.mpr ?_
        exact ⟨c, Finset.mem_univ c, by simp [margin]⟩
      exact Finset.le_max' _ _ hmem0
    have hmax_eq : Finset.max' losses hLosses = 0 :=
      le_antisymm hmax_le_zero (by simpa using hzero_le_max)
    have hdef : maxLoss P c = Finset.max' losses hLosses := by
      simp [maxLoss, hA, losses]
    simp [hdef, hmax_eq]

  -- Any candidate's maximum loss is nonnegative (contains the self-pair with margin 0).
  have hmaxLoss_nonneg : ∀ a : A, 0 ≤ maxLoss P a := by
    intro a
    classical
    set losses : Finset Int := Finset.univ.image (fun b : A => margin P b a)
    have hLosses : losses.Nonempty := by
      rcases hA with ⟨b, hb⟩
      exact ⟨margin P b a, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    have hmem0 : 0 ∈ losses := by
      refine Finset.mem_image.mpr ?_
      exact ⟨a, Finset.mem_univ a, by simp [margin]⟩
    have hle : 0 ≤ Finset.max' losses hLosses := Finset.le_max' _ _ hmem0
    have hdef : maxLoss P a = Finset.max' losses hLosses := by
      simp [maxLoss, hA, losses]
    simpa [hdef] using hle

  -- Any other candidate loses to `c`, so its maximum loss is strictly positive.
  have hmaxLoss_pos_of_ne : ∀ {x : A}, x ≠ c → 0 < maxLoss P x := by
    intro x hx
    classical
    set losses : Finset Int := Finset.univ.image (fun b : A => margin P b x)
    have hLosses : losses.Nonempty := by
      rcases hA with ⟨b, hb⟩
      exact ⟨margin P b x, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    have hpos_margin : 0 < margin P c x := by
      have : margin_pos P c x :=
        (CondorcetWinner_iff_margin_pos P c).mp hw x (by simpa [eq_comm] using hx)
      simpa [margin_pos] using this
    have hmem : margin P c x ∈ losses := by
      refine Finset.mem_image.mpr ?_
      exact ⟨c, Finset.mem_univ c, rfl⟩
    have hle : margin P c x ≤ Finset.max' losses hLosses :=
      Finset.le_max' _ _ hmem
    have hpos : 0 < Finset.max' losses hLosses := lt_of_lt_of_le hpos_margin hle
    have hdef : maxLoss P x = Finset.max' losses hLosses := by
      simp [maxLoss, hA, losses]
    simpa [hdef] using hpos

  -- Compute the minimax score: all scores are ≥ 0 and `c` achieves 0.
  have hminScore : minimaxScore P = 0 := by
    classical
    set scores : Finset Int := Finset.univ.image (fun a : A => maxLoss P a)
    have hScores : scores.Nonempty := by
      rcases hA with ⟨a, ha⟩
      exact ⟨maxLoss P a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    have hmem0 : maxLoss P c ∈ scores := by
      refine Finset.mem_image.mpr ?_
      exact ⟨c, Finset.mem_univ c, rfl⟩
    have hdef : minimaxScore P = Finset.min' scores hScores := by
      simp [minimaxScore, hA, scores]
    have hmin_le : Finset.min' scores hScores ≤ maxLoss P c :=
      Finset.min'_le (s := scores) (H2 := hmem0)
    have hnonneg' : 0 ≤ Finset.min' scores hScores := by
      have hmemMin : Finset.min' scores hScores ∈ scores := Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmemMin with ⟨a, _, hEq⟩
      exact hEq ▸ hmaxLoss_nonneg a
    have hmin_le' : minimaxScore P ≤ maxLoss P c := by simpa [hdef] using hmin_le
    have hnonneg : 0 ≤ minimaxScore P := by simpa [hdef] using hnonneg'
    have h0 : maxLoss P c = 0 := hmaxLoss_c_zero
    have hle : minimaxScore P ≤ 0 := by simpa [h0] using hmin_le'
    exact le_antisymm hle hnonneg

  -- Winners are exactly the zero-max-loss candidates, which is only `c`.
  have hsetBase : minimax P =
      Finset.univ.filter (fun a : A => maxLoss P a = minimaxScore P) := by
    simp [minimax, hnonempty]
  have hset : minimax P =
      Finset.univ.filter (fun a : A => maxLoss P a = 0) := by
    simpa [hminScore] using hsetBase

  have hmem_c : c ∈ minimax P := by
    have hmem_filter : c ∈ Finset.univ.filter (fun a : A => maxLoss P a = 0) := by
      simp [hmaxLoss_c_zero]
    simpa [hset] using hmem_filter

  -- Show uniqueness.
  have huniq : minimax P ⊆ {c} := by
    intro x hx
    have hx' : x ∈ Finset.univ.filter (fun a : A => maxLoss P a = 0) := by
      simpa [hset] using hx
    have hzero : maxLoss P x = 0 := (Finset.mem_filter.mp hx').2
    by_cases hxc : x = c
    · simp [hxc]
    · have hpos := hmaxLoss_pos_of_ne hxc
      have : False := by linarith
      cases this

  -- Finish: set equality with the singleton {c}.
  apply Finset.ext
  intro x
  constructor
  · intro hx; exact huniq hx
  · intro hx
    have : x = c := by simpa using hx
    subst this; simpa using hmem_c

end SocialChoice
