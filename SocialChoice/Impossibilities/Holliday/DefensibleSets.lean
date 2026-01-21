import Mathlib.Tactic
import SocialChoice.Impossibilities.Holliday.CondorcetLosers
import SocialChoice.Impossibilities.Holliday.DefensibleSlack
import SocialChoice.Rules.DefensibleSet.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

lemma margin_P1Profile_d_c : margin P1Profile d c = (-44 : Int) := by
  have h := (margin_antisymmetric (P := P1Profile)) d c
  simp [margin_P1Profile_c_d] at h
  exact h

lemma margin_P1Profile_e_c : margin P1Profile e c = (-88 : Int) := by
  have h := (margin_antisymmetric (P := P1Profile)) e c
  simp [margin_P1Profile_c_e] at h
  exact h

lemma defensible_P1_a : a ∈ defensibleSet P1Profile := by
  classical
  refine (mem_defensibleSet_iff (P := P1Profile) (x := a)).2 ?_
  intro y
  fin_cases y
  · refine ⟨a, ?_⟩
    simp [self_margin_zero]
  · refine ⟨e, ?_⟩
    simp [margin_P1Profile_e_b, margin_P1Profile_b_a]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_c, margin_P1Profile_c_a]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_d, margin_P1Profile_d_a]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_e, margin_P1Profile_e_a]

lemma defensible_P1_d : d ∈ defensibleSet P1Profile := by
  classical
  refine (mem_defensibleSet_iff (P := P1Profile) (x := d)).2 ?_
  intro y
  fin_cases y
  · refine ⟨b, ?_⟩
    simp [margin_P1Profile_b_a, margin_P1Profile_a_d]
  · refine ⟨e, ?_⟩
    simp [margin_P1Profile_e_b, margin_P1Profile_b_d]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_c, margin_P1Profile_c_d]
  · refine ⟨a, ?_⟩
    simp [self_margin_zero, margin_P1Profile_a_d]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_e, margin_P1Profile_e_d]

lemma not_defensible_P1_b : b ∉ defensibleSet P1Profile := by
  classical
  intro hb
  have hb' := (mem_defensibleSet_iff (P := P1Profile) (x := b)).1 hb
  rcases hb' e with ⟨z, hz⟩
  fin_cases z
  · have hz' : (46 : Int) ≥ 92 := by
      simp [margin_P1Profile_a_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (46 : Int) ≥ 92) hz'
  · have hz' : (-92 : Int) ≥ 92 := by
      simp [margin_P1Profile_b_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (-92 : Int) ≥ 92) hz'
  · have hz' : (88 : Int) ≥ 92 := by
      simp [margin_P1Profile_c_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (88 : Int) ≥ 92) hz'
  · have hz' : (-8 : Int) ≥ 92 := by
      simp [margin_P1Profile_d_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (-8 : Int) ≥ 92) hz'
  · have hz' : (0 : Int) ≥ 92 := by
      simp [self_margin_zero, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (0 : Int) ≥ 92) hz'

lemma not_defensible_P1_c : c ∉ defensibleSet P1Profile := by
  classical
  intro hc
  have hc' := (mem_defensibleSet_iff (P := P1Profile) (x := c)).1 hc
  rcases hc' a with ⟨z, hz⟩
  fin_cases z
  · have hz' : (0 : Int) ≥ 86 := by
      simp [self_margin_zero, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (0 : Int) ≥ 86) hz'
  · have hz' : (84 : Int) ≥ 86 := by
      simp [margin_P1Profile_b_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (84 : Int) ≥ 86) hz'
  · have hz' : (-86 : Int) ≥ 86 := by
      simp [margin_P1Profile_c_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (-86 : Int) ≥ 86) hz'
  · have hz' : (-2 : Int) ≥ 86 := by
      simp [margin_P1Profile_d_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (-2 : Int) ≥ 86) hz'
  · have hz' : (-46 : Int) ≥ 86 := by
      simp [margin_P1Profile_e_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (-46 : Int) ≥ 86) hz'

lemma not_defensible_P1_e : e ∉ defensibleSet P1Profile := by
  classical
  intro he
  have he' := (mem_defensibleSet_iff (P := P1Profile) (x := e)).1 he
  rcases he' c with ⟨z, hz⟩
  fin_cases z
  · have hz' : (86 : Int) ≥ 88 := by
      simp [margin_P1Profile_a_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (86 : Int) ≥ 88) hz'
  · have hz' : (42 : Int) ≥ 88 := by
      simp [margin_P1Profile_b_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (42 : Int) ≥ 88) hz'
  · have hz' : (0 : Int) ≥ 88 := by
      simp [self_margin_zero, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (0 : Int) ≥ 88) hz'
  · have hz' : (-44 : Int) ≥ 88 := by
      simp [margin_P1Profile_d_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (-44 : Int) ≥ 88) hz'
  · have hz' : (-88 : Int) ≥ 88 := by
      simp [margin_P1Profile_e_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (-88 : Int) ≥ 88) hz'

lemma defensibleSet_P1 : defensibleSet P1Profile = ({a, d} : Finset A5) := by
  classical
  ext x
  fin_cases x
  · simp [defensible_P1_a, a, d]
  · simp [not_defensible_P1_b, a, d]
  · simp [not_defensible_P1_c, a, d]
  · simp [defensible_P1_d, a, d]
  · simp [not_defensible_P1_e, a, d]

end Holliday

end SocialChoice
