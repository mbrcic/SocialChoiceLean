import SocialChoice.Axioms.Participation
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

theorem split_cycle_positive_involvement : PositiveInvolvement splitCycle := by
  intro U A _ _ V u hu P Q x hagree hx htop
  classical
  let ballot := Q.pref (newVoter (u := u) (V := V) hu)
  have hxcond : ∀ y, ¬ splitCycleDefeats P y x := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ x, ?_⟩
  intro y hy
  have hdef' : splitCycleDefeats P y x := by
    rcases hy with ⟨hpos', hnocycle'⟩
    have hne : y ≠ x := ne_of_margin_pos (P := Q) hpos'
    have hxy : ballot.lt x y := htop y hne
    have hmargin : margin Q y x = margin P y x - 1 :=
      margin_add_newVoter_eq_of_prefers_rev (u := u) (V := V) hu P Q hagree y x hxy
    have hpos : margin_pos P y x := by
      have hpos' : 0 < margin Q y x := by
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
          cycle (fun a b => margin Q y x ≤ margin Q a b) l := by
        refine cycle_of_cycle_imp ?_ hcycle
        intro a b hab
        have hle : margin P a b ≤ margin Q a b + 1 :=
          margin_le_add_newVoter (u := u) (V := V) hu P Q hagree a b
        have hrel : margin P y x - 1 ≤ margin Q a b := by
          linarith [hab, hle]
        simpa [hmargin] using hrel
      exact hnocycle' ⟨l, hymem, hxmem, hcycle'⟩
    exact ⟨hpos, hnocycle⟩
  exact (hxcond y) hdef'

theorem split_cycle_negative_involvement : NegativeInvolvement splitCycle := by
  intro U A _ _ V u hu P Q x hagree hx hbottom
  classical
  let ballot := Q.pref (newVoter (u := u) (V := V) hu)
  have hnotall : ¬ ∀ y, ¬ splitCycleDefeats P y x := by
    intro hAll
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAll⟩)
  obtain ⟨y, hydef'⟩ := not_forall.mp hnotall
  have hydef : splitCycleDefeats P y x := by
    exact not_not.mp hydef'
  by_contra hxmem
  have hxcond : ∀ y, ¬ splitCycleDefeats Q y x :=
    (Finset.mem_filter.mp hxmem).2
  have hydef' : splitCycleDefeats Q y x := by
    rcases hydef with ⟨hpos, hnocycle⟩
    have hne : y ≠ x := ne_of_margin_pos (P := P) hpos
    have hxy : ballot.lt y x := hbottom y hne
    have hmargin : margin Q y x = margin P y x + 1 :=
      margin_add_newVoter_eq_of_prefers (u := u) (V := V) hu P Q hagree y x hxy
    have hpos' : margin_pos Q y x := by
      have hpos' : 0 < margin Q y x := by
        have hpos0 : 0 < margin P y x := by
          simpa [margin_pos] using hpos
        linarith [hpos0, hmargin]
      simpa [margin_pos] using hpos'
    have hnocycle' :
        ¬ ∃ l, y ∈ l ∧ x ∈ l ∧
          cycle (fun a b => margin Q y x ≤ margin Q a b) l := by
      intro hcyc
      rcases hcyc with ⟨l, hymem, hxmem, hcycle⟩
      have hcycle' :
          cycle (fun a b => margin P y x ≤ margin P a b) l := by
        refine cycle_of_cycle_imp ?_ hcycle
        intro a b hab
        have hle : margin Q a b ≤ margin P a b + 1 :=
          margin_add_newVoter_le (u := u) (V := V) hu P Q hagree a b
        have hrel : margin P y x + 1 ≤ margin P a b + 1 := by
          linarith [hab, hle, hmargin]
        exact (add_le_add_iff_right 1).1 hrel
      exact hnocycle ⟨l, hymem, hxmem, hcycle'⟩
    exact ⟨hpos', hnocycle'⟩
  exact (hxcond y) hydef'

end SocialChoice
