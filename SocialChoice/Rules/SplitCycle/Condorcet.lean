import SocialChoice.Axioms.Condorcet
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

-- Technical lemma for Split Cycle proofs
lemma no_margin_pos_cycle_of_CondorcetWinner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    CondorcetWinner P c → ¬ ∃ l, cycle (margin_pos P) l ∧ c ∈ l := by
  intro hw hcyc
  rcases hcyc with ⟨l, hcycle, hwmem⟩
  have hdom := dominate_of_cycle l (margin_pos P) hcycle c hwmem
  rcases hdom with ⟨y, _hy_mem, hyw⟩
  have hne : y ≠ c := by
    intro hEq
    subst hEq
    exact (margin_pos_irrefl (P := P) y) hyw
  have hwy : margin_pos P c y := by
    have := (CondorcetWinner_iff_margin_pos P c).mp hw y (by simpa [eq_comm] using hne)
    exact this
  exact (margin_pos_asymm (P := P) c y hwy) hyw

theorem split_cycle_condorcet_consistency : CondorcetConsistency splitCycle := by
  intro V A _ _ P c hw
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxcond : ∀ y, ¬ splitCycleDefeats P y x := (Finset.mem_filter.mp hx).2
    by_cases h : x = c
    · simp [h]
    · have hdef : splitCycleDefeats P c x := by
        have hpos : margin_pos P c x := by
          have := (CondorcetWinner_iff_margin_pos P c).mp hw x (by simpa [eq_comm] using h)
          exact this
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
        have hno := no_margin_pos_cycle_of_CondorcetWinner P c hw
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
      · have hwy : margin_pos P c y := by
          have := (CondorcetWinner_iff_margin_pos P c).mp hw y (by simpa [eq_comm] using h)
          exact this
        exact (margin_pos_asymm (P := P) c y hwy) hypos
    exact (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hwcond⟩)

theorem split_cycle_CondorcetLoser_criterion :
    CondorcetLoserCriterion splitCycle := by
  intro V A _ _ P x hloser
  classical
  by_contra hxmem
  have hxcond : ∀ z, ¬ splitCycleDefeats P z x := (Finset.mem_filter.mp hxmem).2
  rcases hloser.2 with ⟨y, hyne⟩
  have hypos : margin_pos P y x := by
    exact (CondorcetLoser_iff_margin_pos P x).mp hloser |>.1 y (Ne.symm hyne)
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
      · have hpos : margin_pos P z x := by
          exact (CondorcetLoser_iff_margin_pos P x).mp hloser |>.1 z (by simpa [eq_comm] using hz)
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
