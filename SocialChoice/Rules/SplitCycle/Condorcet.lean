import SocialChoice.Axioms.Condorcet
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

theorem split_cycle_condorcet_criterion : condorcet_criterion splitCycle := by
  intro V A _ _ P c hw
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxcond : ∀ y, ¬ splitCycleDefeats P y x := (Finset.mem_filter.mp hx).2
    by_cases h : x = c
    · simpa [h]
    · have hdef : splitCycleDefeats P c x := by
        have hpos : margin_pos P c x := hw x (by simpa [eq_comm] using h)
        refine ⟨hpos, ?_⟩
        intro hcyc
        rcases hcyc with ⟨l, hwmem, hxmem, hcycle⟩
        have hpos' : 0 < margin P c x := by
          simpa [margin_pos] using hpos
        have hcycle' : cycle (margin_pos P) l := by
          refine cycle_of_cycle_imp ?_ hcycle
          intro a b hab
          have hlt : 0 < margin P a b := lt_of_lt_of_le hpos' hab
          simpa [margin_pos] using hlt
        have hno := no_margin_pos_cycle_of_condorcet P c hw
        exact hno ⟨l, hcycle', hwmem⟩
      exfalso
      exact (hxcond c) hdef
  · intro hx
    have hx' : x = c := by simpa using hx
    subst x
    have hwcond : ∀ y, ¬ splitCycleDefeats P y c := by
      intro y hy
      rcases hy with ⟨hypos, _⟩
      by_cases h : y = c
      · subst h
        exact (margin_pos_irrefl (P := P) y) hypos
      · have hwy : margin_pos P c y := hw y (by simpa [eq_comm] using h)
        exact (margin_pos_asymm (P := P) c y hwy) hypos
    exact (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hwcond⟩)

theorem split_cycle_condorcet_loser_criterion :
    condorcet_loser_criterion splitCycle := by
  intro V A _ _ P x hloser
  classical
  rcases hloser with ⟨hlose, ⟨y, hyne⟩⟩
  by_contra hxmem
  have hxcond : ∀ z, ¬ splitCycleDefeats P z x := (Finset.mem_filter.mp hxmem).2
  have hypos : margin_pos P y x := hlose y hyne
  have hdef : splitCycleDefeats P y x := by
    refine ⟨hypos, ?_⟩
    intro hcyc
    rcases hcyc with ⟨l, hymem, hxmem', hcycle⟩
    have hlen : 0 < l.length := length_cycle_pos hcycle
    obtain ⟨i, hi, hix⟩ : ∃ i : Nat, ∃ hi : i < l.length, l[i]'hi = x := by
      have hx' : ∃ z ∈ l, z = x := ⟨x, hxmem', rfl⟩
      rcases (List.exists_mem_iff_getElem (l := l) (p := fun z => z = x)).1 hx' with
        ⟨i, hi, hix⟩
      exact ⟨i, hi, by simpa using hix⟩
    have hmod : (i + 1) % l.length < l.length := Nat.mod_lt _ hlen
    have hrel :
        margin P y x ≤ margin P (l[i]'hi) (l[(i + 1) % l.length]'hmod) := by
      simpa using
        (dominates_of_cycle_index l (fun a b => margin P y x ≤ margin P a b)
          hcycle i hi hmod)
    have hrel' : margin P y x ≤ margin P x (l[(i + 1) % l.length]'hmod) := by
      simpa [hix] using hrel
    set z : A := l[(i + 1) % l.length]'hmod
    have hrel'' : margin P y x ≤ margin P x z := by
      simpa [z] using hrel'
    have hzx : margin P x z ≤ 0 := by
      by_cases hz : z = x
      · subst hz
        simp [self_margin_zero]
      · have hpos : margin_pos P z x := hlose z (by simpa [eq_comm] using hz)
        have hpos' : 0 < margin P z x := by
          simpa [margin_pos] using hpos
        have hskew : margin P x z = - margin P z x := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P)) x z
        have hneg : margin P x z < 0 := by
          simpa [hskew] using (neg_neg_of_pos hpos')
        exact le_of_lt hneg
    have hle0 : margin P y x ≤ 0 := le_trans hrel'' hzx
    have hypos' : 0 < margin P y x := by
      simpa [margin_pos] using hypos
    exact (not_lt_of_ge hle0 hypos')
  exact (hxcond y) hdef

end SocialChoice
