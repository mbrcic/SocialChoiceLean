import Mathlib.Tactic
import SocialChoice.Impossibilities.Holliday.Margins
import SocialChoice.Axioms.Condorcet

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

lemma margin_P1Profile_c_a : margin P1Profile c a = (-86 : Int) := by
  calc
    margin P1Profile c a = - margin P1Profile a c :=
      (margin_antisymmetric (P := P1Profile)) c a
    _ = (-86 : Int) := by simp [margin_P1Profile_a_c]

lemma margin_P1Profile_d_a : margin P1Profile d a = (-2 : Int) := by
  calc
    margin P1Profile d a = - margin P1Profile a d :=
      (margin_antisymmetric (P := P1Profile)) d a
    _ = (-2 : Int) := by simp [margin_P1Profile_a_d]

lemma margin_P1Profile_e_a : margin P1Profile e a = (-46 : Int) := by
  calc
    margin P1Profile e a = - margin P1Profile a e :=
      (margin_antisymmetric (P := P1Profile)) e a
    _ = (-46 : Int) := by simp [margin_P1Profile_a_e]

lemma margin_P1Profile_e_b : margin P1Profile e b = 92 := by
  calc
    margin P1Profile e b = - margin P1Profile b e :=
      (margin_antisymmetric (P := P1Profile)) e b
    _ = 92 := by simp [margin_P1Profile_b_e]

lemma margin_P1Profile_e_d : margin P1Profile e d = 8 := by
  calc
    margin P1Profile e d = - margin P1Profile d e :=
      (margin_antisymmetric (P := P1Profile)) e d
    _ = 8 := by simp [margin_P1Profile_d_e]

lemma P1_condorcetLoser_d : CondorcetLoser P1Profile d := by
  refine (CondorcetLoser_iff_margin_pos (P := P1Profile) (c := d)).2 ?_
  refine ⟨?h, ?ne⟩
  · intro x hx
    fin_cases x <;> try cases hx rfl
    · simp [margin_pos, margin_P1Profile_a_d]
    · simp [margin_pos, margin_P1Profile_b_d]
    · simp [margin_pos, margin_P1Profile_c_d]
    · simp [margin_pos, margin_P1Profile_e_d]
  · exact ⟨a, by decide⟩

lemma P1_not_condorcetLoser_a : ¬ CondorcetLoser P1Profile a := by
  intro h
  have h' := (CondorcetLoser_iff_margin_pos (P := P1Profile) (c := a)).1 h
  have hpos := h'.1 c (by decide)
  have hcontra : ¬ margin_pos P1Profile c a := by
    simp [margin_pos, margin_P1Profile_c_a]
  exact hcontra hpos

end Holliday

end SocialChoice
