import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.ListBallot
import SocialChoice.Rules.Nanson.Condorcet
import SocialChoice.Rules.Nanson.Reversal

namespace SocialChoice

open Finset
open scoped BigOperators

abbrev A3 := Fin 3
abbrev a : A3 := 0
abbrev b : A3 := 1
abbrev c : A3 := 2

private def ballot_bca : ListBallot 3 := ListBallot.mk' [1, 2, 0]
private def ballot_abc : ListBallot 3 := ListBallot.identity 3
private def ballot_cab : ListBallot 3 := ListBallot.mk' [2, 0, 1]
private def ballot_acb : ListBallot 3 := ListBallot.mk' [0, 2, 1]

private def blocks1 : List (Nat × ListBallot 3) :=
  [(2, ballot_bca), (3, ballot_abc), (3, ballot_cab)]

private def blocks2 : List (Nat × ListBallot 3) :=
  [(2, ballot_acb), (1, ballot_cab)]

private def blocks3 : List (Nat × ListBallot 3) :=
  [(2, ballot_bca), (3, ballot_abc), (4, ballot_cab), (2, ballot_acb)]

noncomputable def nansonProfile1 : Profile (Fin (ballotList blocks1).length) A3 :=
  profileOfBlocks blocks1

noncomputable def nansonProfile2 : Profile (Fin (ballotList blocks2).length) A3 :=
  profileOfBlocks blocks2

noncomputable def nansonProfile3 : Profile (Fin (ballotList blocks3).length) A3 :=
  profileOfBlocks blocks3

private lemma blocks1_margin_a_b : marginBlocks blocks1 a b = 4 := by decide
private lemma blocks1_margin_a_c : marginBlocks blocks1 a c = -2 := by decide
private lemma blocks1_margin_b_c : marginBlocks blocks1 b c = 2 := by decide

private lemma blocks2_margin_a_b : marginBlocks blocks2 a b = 3 := by decide
private lemma blocks2_margin_a_c : marginBlocks blocks2 a c = 1 := by decide

private lemma blocks3_margin_c_a : marginBlocks blocks3 c a = 1 := by decide
private lemma blocks3_margin_c_b : marginBlocks blocks3 c b = 1 := by decide

private lemma profile1_margin_a_b : margin nansonProfile1 a b = 4 := by
  calc
    margin nansonProfile1 a b = marginBlocks blocks1 a b := by
      simpa [nansonProfile1] using
        (margin_profileOfBlocks (blocks := blocks1) (a := a) (b := b) (hne := by decide))
    _ = 4 := blocks1_margin_a_b

private lemma profile1_margin_a_c : margin nansonProfile1 a c = -2 := by
  calc
    margin nansonProfile1 a c = marginBlocks blocks1 a c := by
      simpa [nansonProfile1] using
        (margin_profileOfBlocks (blocks := blocks1) (a := a) (b := c) (hne := by decide))
    _ = -2 := blocks1_margin_a_c

private lemma profile1_margin_b_c : margin nansonProfile1 b c = 2 := by
  calc
    margin nansonProfile1 b c = marginBlocks blocks1 b c := by
      simpa [nansonProfile1] using
        (margin_profileOfBlocks (blocks := blocks1) (a := b) (b := c) (hne := by decide))
    _ = 2 := blocks1_margin_b_c

private lemma profile1_margin_b_a : margin nansonProfile1 b a = -4 := by
  have h := (margin_antisymmetric (P := nansonProfile1) b a)
  simpa [profile1_margin_a_b] using h

private lemma profile1_margin_c_a : margin nansonProfile1 c a = 2 := by
  have h := (margin_antisymmetric (P := nansonProfile1) c a)
  simpa [profile1_margin_a_c] using h

private lemma profile1_margin_c_b : margin nansonProfile1 c b = -2 := by
  have h := (margin_antisymmetric (P := nansonProfile1) c b)
  simpa [profile1_margin_b_c] using h

private lemma profile1_c2Borda_a : c2BordaScore nansonProfile1 a = 2 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, profile1_margin_a_b,
    profile1_margin_a_c]

private lemma profile1_c2Borda_b : c2BordaScore nansonProfile1 b = -2 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, profile1_margin_b_a,
    profile1_margin_b_c]

private lemma profile1_c2Borda_c : c2BordaScore nansonProfile1 c = 0 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, profile1_margin_c_a,
    profile1_margin_c_b]

private lemma profile1_pos_iff (x : Fin 3) : 0 < c2BordaScore nansonProfile1 x ↔ x = a := by
  fin_cases x <;> simp [profile1_c2Borda_a, profile1_c2Borda_b, profile1_c2Borda_c, a]

lemma nanson_profile1 : nanson nansonProfile1 = {a} := by
  classical
  have hnotall : ¬ ∀ x, c2BordaScore nansonProfile1 x = 0 := by
    intro hall
    have := hall a
    linarith [profile1_c2Borda_a]
  have hsurv : (Finset.univ.filter (fun x => c2BordaScore nansonProfile1 x > 0)).Nonempty := by
    refine ⟨a, ?_⟩
    simp [profile1_c2Borda_a]
  have hsubset : nanson nansonProfile1 ⊆ {a} := by
    intro x hx
    have hxpos : 0 < c2BordaScore nansonProfile1 x :=
      nanson_score_pos_of_mem (P := nansonProfile1) hnotall hsurv hx
    have hx' : x = a := (profile1_pos_iff x).1 hxpos
    simp [hx']
  have hnonempty : (nanson nansonProfile1).Nonempty := by
    simpa using (nanson_isVotingRule (P := nansonProfile1))
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = a := by
    have : x ∈ ({a} : Finset (Fin 3)) := hsubset hx
    simpa using this
  have ha : a ∈ nanson nansonProfile1 := by
    simpa [hx'] using hx
  apply (Finset.eq_singleton_iff_unique_mem).2
  refine ⟨ha, ?_⟩
  intro y hy
  have : y ∈ ({a} : Finset (Fin 3)) := hsubset hy
  simpa using this

private lemma profile2_margin_a_b : margin nansonProfile2 a b = 3 := by
  calc
    margin nansonProfile2 a b = marginBlocks blocks2 a b := by
      simpa [nansonProfile2] using
        (margin_profileOfBlocks (blocks := blocks2) (a := a) (b := b) (hne := by decide))
    _ = 3 := blocks2_margin_a_b

private lemma profile2_margin_a_c : margin nansonProfile2 a c = 1 := by
  calc
    margin nansonProfile2 a c = marginBlocks blocks2 a c := by
      simpa [nansonProfile2] using
        (margin_profileOfBlocks (blocks := blocks2) (a := a) (b := c) (hne := by decide))
    _ = 1 := blocks2_margin_a_c

private lemma profile2_condorcet : CondorcetWinner nansonProfile2 a := by
  refine (CondorcetWinner_iff_margin_pos (P := nansonProfile2) (c := a)).2 ?_
  intro d hne
  fin_cases d
  · cases hne rfl
  ·
    have hmargin : margin nansonProfile2 a b = 3 := profile2_margin_a_b
    simp [margin_pos, hmargin]
  ·
    have hmargin : margin nansonProfile2 a c = 1 := profile2_margin_a_c
    simp [margin_pos, hmargin]

lemma nanson_profile2 : nanson nansonProfile2 = {a} := by
  exact nanson_condorcet_consistency nansonProfile2 a profile2_condorcet

private lemma profile3_margin_c_a : margin nansonProfile3 c a = 1 := by
  calc
    margin nansonProfile3 c a = marginBlocks blocks3 c a := by
      simpa [nansonProfile3] using
        (margin_profileOfBlocks (blocks := blocks3) (a := c) (b := a) (hne := by decide))
    _ = 1 := blocks3_margin_c_a

private lemma profile3_margin_c_b : margin nansonProfile3 c b = 1 := by
  calc
    margin nansonProfile3 c b = marginBlocks blocks3 c b := by
      simpa [nansonProfile3] using
        (margin_profileOfBlocks (blocks := blocks3) (a := c) (b := b) (hne := by decide))
    _ = 1 := blocks3_margin_c_b

private lemma profile3_condorcet : CondorcetWinner nansonProfile3 c := by
  refine (CondorcetWinner_iff_margin_pos (P := nansonProfile3) (c := c)).2 ?_
  intro d hne
  fin_cases d
  ·
    have hmargin : margin nansonProfile3 c a = 1 := profile3_margin_c_a
    simp [margin_pos, hmargin]
  ·
    have hmargin : margin nansonProfile3 c b = 1 := profile3_margin_c_b
    simp [margin_pos, hmargin]
  · cases hne rfl

lemma nanson_profile3 : nanson nansonProfile3 = {c} := by
  exact nanson_condorcet_consistency nansonProfile3 c profile3_condorcet

/-- The explicit counterexample: two profiles pick `a`, their combination picks `c`. -/
theorem nanson_subsetReinforcement_counterexample :
    nanson nansonProfile1 = {a} ∧
    nanson nansonProfile2 = {a} ∧
    nanson nansonProfile3 = {c} := by
  exact ⟨nanson_profile1, nanson_profile2, nanson_profile3⟩

/-- As sets, the example violates the subset-reinforcement inclusion. -/
theorem nanson_subsetReinforcement_counterexample_sets :
    ¬ (nanson nansonProfile1 ∩ nanson nansonProfile2 ⊆ nanson nansonProfile3) := by
  intro hsubset
  have ha : (a : Fin 3) ∈ nanson nansonProfile1 ∩ nanson nansonProfile2 := by
    simp [nanson_profile1, nanson_profile2]
  have ha' := hsubset ha
  simp [nanson_profile3] at ha'
  have hne : (a : Fin 3) ≠ c := by decide
  exact hne ha'

end SocialChoice
