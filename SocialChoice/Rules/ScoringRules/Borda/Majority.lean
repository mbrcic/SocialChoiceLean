import SocialChoice.Axioms.Majority
import SocialChoice.Examples
import SocialChoice.Rules.ScoringRules.Borda.Defs

namespace SocialChoice

open Finset

lemma strictMajority_fin3 {S : Finset (Fin 3)} (hcard : S.card = 2) :
    StrictMajority S := by
  unfold StrictMajority
  have h : (2 * (2 : Nat) > (3 : Nat)) := by decide
  simpa [hcard] using h

lemma exampleProfile_strictMajority_top0 :
    StrictMajority (votersTop Examples.exampleProfile 0) := by
  have hcount : countTop (fun v => (Examples.exampleBallots v).ranking) 0 = 2 := rfl
  have hcard : (votersTop Examples.exampleProfile 0).card = 2 := by
    simpa [Examples.exampleProfile_eq, votersTop_card_eq_countTop] using hcount
  exact strictMajority_fin3 hcard

lemma exampleProfile_borda_has_b : (1 : Fin 3) ∈ borda Examples.exampleProfile := by
  decide

theorem borda_not_majorityCriterion : ¬ MajorityCriterion borda := by
  intro hmaj
  have hmaj' : StrictMajority (votersTop Examples.exampleProfile 0) :=
    exampleProfile_strictMajority_top0
  have hres : borda Examples.exampleProfile = {0} :=
    hmaj Examples.exampleProfile 0 hmaj'
  have hb : (1 : Fin 3) ∈ borda Examples.exampleProfile := exampleProfile_borda_has_b
  have hb' : (1 : Fin 3) ∈ ({0} : Finset (Fin 3)) := by
    simpa [hres] using hb
  simp at hb'

end SocialChoice
