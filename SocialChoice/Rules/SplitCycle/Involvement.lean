import SocialChoice.Axioms.Participation
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

theorem split_cycle_positive_involvement : PositiveInvolvement splitCycle := by
  intro V A _ _ P x ballot hx htop
  classical
  have hxcond : ∀ y, ¬ splitCycleDefeats P y x := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ x, ?_⟩
  intro y hy
  have hdef' : splitCycleDefeats P y x := by
    rcases hy with ⟨hpos', hnocycle'⟩
    have hne : y ≠ x := ne_of_margin_pos (P := addVoter P ballot) hpos'
    have hxy : ballot.lt x y := htop y hne
    have hmargin : margin (addVoter P ballot) y x = margin P y x - 1 :=
      margin_addVoter_eq_of_prefers_rev P ballot y x hxy
    have hpos : margin_pos P y x := by
      have hpos' : 0 < margin (addVoter P ballot) y x := by
        simpa [margin_pos] using hpos'
      have hpos'' : 0 < margin P y x := by
        linarith [hpos', hmargin]
      simpa [margin_pos] using hpos''
    have hnocycle :
        ¬ ∃ l, y ∈ l ∧ x ∈ l ∧
          cycle (fun a b => margin P y x ≤ margin P a b) l := by
      intro hcyc
      rcases hcyc with ⟨l, hymem, hxmem, hcycle⟩
      have hcycle' :
          cycle (fun a b => margin (addVoter P ballot) y x ≤
            margin (addVoter P ballot) a b) l := by
        refine cycle_of_cycle_imp ?_ hcycle
        intro a b hab
        have hle : margin P a b ≤ margin (addVoter P ballot) a b + 1 :=
          margin_le_addVoter P ballot a b
        have hrel : margin P y x - 1 ≤ margin (addVoter P ballot) a b := by
          linarith [hab, hle]
        simpa [hmargin] using hrel
      exact hnocycle' ⟨l, hymem, hxmem, hcycle'⟩
    exact ⟨hpos, hnocycle⟩
  exact (hxcond y) hdef'

theorem split_cycle_negative_involvement : NegativeInvolvement splitCycle := by
  intro V A _ _ P x ballot hx hbottom
  classical
  have hnotall : ¬ ∀ y, ¬ splitCycleDefeats P y x := by
    intro hAll
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAll⟩)
  obtain ⟨y, hydef'⟩ := not_forall.mp hnotall
  have hydef : splitCycleDefeats P y x := by
    exact not_not.mp hydef'
  by_contra hxmem
  have hxcond : ∀ y, ¬ splitCycleDefeats (addVoter P ballot) y x :=
    (Finset.mem_filter.mp hxmem).2
  have hydef' : splitCycleDefeats (addVoter P ballot) y x := by
    rcases hydef with ⟨hpos, hnocycle⟩
    have hne : y ≠ x := ne_of_margin_pos (P := P) hpos
    have hxy : ballot.lt y x := hbottom y hne
    have hmargin : margin (addVoter P ballot) y x = margin P y x + 1 :=
      margin_addVoter_eq_of_prefers P ballot y x hxy
    have hpos' : margin_pos (addVoter P ballot) y x := by
      have hpos' : 0 < margin (addVoter P ballot) y x := by
        have hpos0 : 0 < margin P y x := by
          simpa [margin_pos] using hpos
        linarith [hpos0, hmargin]
      simpa [margin_pos] using hpos'
    have hnocycle' :
        ¬ ∃ l, y ∈ l ∧ x ∈ l ∧
          cycle (fun a b => margin (addVoter P ballot) y x ≤
            margin (addVoter P ballot) a b) l := by
      intro hcyc
      rcases hcyc with ⟨l, hymem, hxmem, hcycle⟩
      have hcycle' :
          cycle (fun a b => margin P y x ≤ margin P a b) l := by
        refine cycle_of_cycle_imp ?_ hcycle
        intro a b hab
        have hle : margin (addVoter P ballot) a b ≤ margin P a b + 1 :=
          margin_addVoter_le P ballot a b
        have hrel : margin P y x + 1 ≤ margin P a b + 1 := by
          linarith [hab, hle, hmargin]
        exact (add_le_add_iff_right 1).1 hrel
      exact hnocycle ⟨l, hymem, hxmem, hcycle'⟩
    exact ⟨hpos', hnocycle'⟩
  exact (hxcond y) hydef'

end SocialChoice
