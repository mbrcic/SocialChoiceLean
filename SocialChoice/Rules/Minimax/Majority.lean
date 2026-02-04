import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Majority
import SocialChoice.ListBallot
import SocialChoice.Rules.Minimax.Defs
import SocialChoice.Rules.Minimax.Independence

namespace SocialChoice

open Finset
open MinimaxIndependenceCounterexample

private lemma bottomRank_iff_prefersInList {m n : ℕ} (ballots : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (ballots v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).2 (h d hd)

private lemma minimaxMajorityLoser_votersBottom :
    votersBottom profile (2 : Fin 4) = ({0, 2} : Finset (Fin 3)) := by
  classical
  -- In this profile (see MinimaxIndependenceCounterexample), voters 0 and 2 rank 2 last.
  ext v
  fin_cases v <;>
    simp [votersBottom, profile, ballots, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma minimaxMajorityLoser_strictMajority_bottom2 :
    StrictMajority (votersBottom profile (2 : Fin 4)) := by
  have hcard : (votersBottom profile (2 : Fin 4)).card = 2 := by
    simp [minimaxMajorityLoser_votersBottom]
  simp [StrictMajority, hcard]

theorem minimax_not_majority_loser_criterion : ¬ MajorityLoserCriterion minimax := by
  intro hmaj
  have hmaj' : StrictMajority (votersBottom profile (2 : Fin 4)) :=
    minimaxMajorityLoser_strictMajority_bottom2
  have hne : ∃ d : Fin 4, d ≠ (2 : Fin 4) := by
    exact ⟨0, by decide⟩
  have hforbid : (2 : Fin 4) ∉ minimax profile :=
    hmaj profile (2 : Fin 4) hmaj' hne
  have hwinner : (2 : Fin 4) ∈ minimax profile :=
    minimax_profile_has_2
  exact hforbid hwinner

end SocialChoice
