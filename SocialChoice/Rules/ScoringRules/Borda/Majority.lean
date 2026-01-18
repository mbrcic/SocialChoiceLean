import SocialChoice.Axioms.Majority
import SocialChoice.Examples
import SocialChoice.Rules.ScoringRules.Borda.Defs

namespace SocialChoice

open Finset

section LocalExample

private abbrev Voters3 := Fin 3
private abbrev A3Borda := Fin 3

private def bordaBallot012 : ListBallot 3 := ListBallot.identity 3
private def bordaBallot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]

private def bordaExampleBallots : Voters3 → ListBallot 3
  | 0 => bordaBallot012
  | 1 => bordaBallot012
  | 2 => bordaBallot120

private noncomputable def bordaExampleProfile : Profile Voters3 A3Borda :=
  profileOfListBallots bordaExampleBallots

private lemma bordaExampleProfile_eq :
    bordaExampleProfile = profileOfListBallots bordaExampleBallots := rfl

private lemma bordaExample_top0_count :
    countTop (fun v => (bordaExampleBallots v).ranking) 0 = 2 := rfl

private lemma bordaExample_votersTop_card :
    (votersTop bordaExampleProfile 0).card = 2 := by
  simpa [bordaExampleProfile_eq, votersTop_card_eq_countTop] using
    (bordaExample_top0_count)

private lemma bordaExample_borda_has_one : (1 : Fin 3) ∈ borda bordaExampleProfile := by
  decide

end LocalExample

private lemma strictMajority_fin3 {S : Finset (Fin 3)} (hcard : S.card = 2) :
    StrictMajority S := by
  unfold StrictMajority
  simp [hcard]

private lemma exampleProfile_strictMajority_top0 :
    StrictMajority (votersTop bordaExampleProfile 0) := by
  exact strictMajority_fin3 (by simpa using bordaExample_votersTop_card)

private lemma exampleProfile_borda_has_b : (1 : Fin 3) ∈ borda bordaExampleProfile :=
  bordaExample_borda_has_one

theorem borda_not_majority_criterion : ¬ MajorityCriterion borda := by
  intro hmaj
  have hmaj' : StrictMajority (votersTop bordaExampleProfile 0) :=
    exampleProfile_strictMajority_top0
  have hres : borda bordaExampleProfile = {0} :=
    hmaj bordaExampleProfile 0 hmaj'
  have hb : (1 : Fin 3) ∈ borda bordaExampleProfile := exampleProfile_borda_has_b
  have hb' : (1 : Fin 3) ∈ ({0} : Finset (Fin 3)) := by
    simp [hres] at hb
  simp at hb'

end SocialChoice
