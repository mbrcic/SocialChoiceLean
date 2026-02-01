import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Pareto
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

private def vetoParetoBallot : ListBallot 3 := ListBallot.mk' [0, 1, 2]

private def vetoParetoBallots : Fin 1 → ListBallot 3
  | 0 => vetoParetoBallot

private noncomputable def vetoParetoProfile : Profile (Fin 1) (Fin 3) :=
  profileOfListBallots vetoParetoBallots

private lemma rank_vetoPareto_0 : rank vetoParetoBallot.toLinearOrder (0 : Fin 3) = 0 := by decide
private lemma rank_vetoPareto_1 : rank vetoParetoBallot.toLinearOrder (1 : Fin 3) = 1 := by decide
private lemma rank_vetoPareto_2 : rank vetoParetoBallot.toLinearOrder (2 : Fin 3) = 2 := by decide

private lemma vetoPareto_score (c : Fin 3) :
    scoreCandidate vetoParetoProfile (fun r => vetoScore 3 r) c =
      (if c = 2 then 0 else 1) := by
  fin_cases c <;>
    simp [scoreCandidate, vetoParetoProfile, vetoParetoBallots, profileOfListBallots,
      rank_vetoPareto_0, rank_vetoPareto_1, rank_vetoPareto_2, vetoScore]

private lemma vetoPareto_one_mem : (1 : Fin 3) ∈ veto vetoParetoProfile := by
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    classical
    exact Finset.univ_nonempty
  have h1mem :
      (1 : Fin 3) ∈ scoringWinners vetoParetoProfile (fun r => vetoScore 3 r) := by
    apply
      (scoringWinners_iff_forall_le (P := vetoParetoProfile)
        (score := fun r => vetoScore 3 r) (hA := hA) (c := (1 : Fin 3))).2
    intro d
    fin_cases d <;> simp [vetoPareto_score]
  simpa [veto, scoringRule] using h1mem

theorem veto_not_pareto_efficiency : ¬ ParetoEfficiency veto := by
  intro hpareto
  have hpref : ∀ v : Fin 1, Prefers vetoParetoProfile v (0 : Fin 3) (1 : Fin 3) := by
    intro v
    fin_cases v
    simp [vetoParetoProfile, vetoParetoBallots, prefers_iff_prefersInList, prefersInList]
    decide
  exact (hpareto vetoParetoProfile (0 : Fin 3) (1 : Fin 3) hpref) vetoPareto_one_mem

end SocialChoice
