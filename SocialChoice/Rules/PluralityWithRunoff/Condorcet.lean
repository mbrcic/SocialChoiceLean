import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Condorcet

namespace SocialChoice

open InstantRunoffCondorcetCounterexample

/-!
# Plurality with Runoff fails Condorcet consistency

We reuse the 5-voter, 3-candidate counterexample for IRV and the fact that
IRV equals Plurality with Runoff for at most three candidates.
-/

theorem pluralityWithRunoff_not_condorcet : ¬ CondorcetConsistency pluralityWithRunoff := by
  intro hcond
  have hcw : CondorcetWinner profile (1 : Fin 3) := condorcetWinner_one
  have hsingle := hcond (P := profile) (c := (1 : Fin 3)) hcw
  have hIRV :
      instantRunoffVoting profile = pluralityWithRunoff profile := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (V := Fin 5) (A := Fin 3) (hcard := by decide) (P := profile))
  have hne : (0 : Fin 3) ∈ pluralityWithRunoff profile := by
    have hne' : (0 : Fin 3) ∈ instantRunoffVoting profile := by
      simp [instantRunoffVoting_profile_winner]
    simpa [hIRV] using hne'
  have hcontra : False := by
    simp [hsingle] at hne
  exact hcontra

end SocialChoice
