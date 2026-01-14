import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import SocialChoice.Axioms.Pareto
import SocialChoice.Rank
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

theorem scoringRule_pareto_nonempty (score : Nat → Nat → Int)
    (hstrict : strictlyDecreasingScore score) :
    ParetoEfficiencyNonempty (scoringRule score) := by
  intro V A _ _ _ P c d hpref hd
  classical
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
  have hlt :
      scoreCandidate P scoreFun d < scoreCandidate P scoreFun c := by
    unfold scoreCandidate
    have hle :
        ∀ v ∈ (Finset.univ : Finset V),
          scoreFun (rank (P.pref v) d) ≤ scoreFun (rank (P.pref v) c) := by
      intro v hv
      have hlt_rank : rank (P.pref v) c < rank (P.pref v) d :=
        rank_lt_of_lt (r := P.pref v) (c := c) (d := d) (hpref v)
      exact (hstrict (Fintype.card A) _ _ hlt_rank).le
    have hlt' :
        ∃ v ∈ (Finset.univ : Finset V),
          scoreFun (rank (P.pref v) d) < scoreFun (rank (P.pref v) c) := by
      rcases Classical.choice (inferInstance : Nonempty V) with v0
      refine ⟨v0, by simp, ?_⟩
      have hlt_rank : rank (P.pref v0) c < rank (P.pref v0) d :=
        rank_lt_of_lt (r := P.pref v0) (c := c) (d := d) (hpref v0)
      exact hstrict (Fintype.card A) _ _ hlt_rank
    have hdiff_nonneg :
        ∀ v ∈ (Finset.univ : Finset V),
          0 ≤ scoreFun (rank (P.pref v) c) - scoreFun (rank (P.pref v) d) :=
      by
      intro v hv
      have hv_le := hle v hv
      exact sub_nonneg.mpr hv_le
    have hdiff_pos :
        ∃ v ∈ (Finset.univ : Finset V),
          0 < scoreFun (rank (P.pref v) c) - scoreFun (rank (P.pref v) d) :=
      by
      rcases hlt' with ⟨v, hv, hv_lt⟩
      exact ⟨v, hv, sub_pos.mpr hv_lt⟩
    let diff : V → Int :=
      fun v => scoreFun (rank (P.pref v) c) - scoreFun (rank (P.pref v) d)
    rcases hdiff_pos with ⟨v0, hv0, hv0_pos⟩
    have hsum_rest_nonneg :
        0 ≤ (Finset.univ.erase v0 : Finset V).sum fun v : V => diff v := by
      have hnonneg :
          ∀ v ∈ (Finset.univ.erase v0 : Finset V), 0 ≤ diff v := by
        intro v hv
        exact hdiff_nonneg _ (Finset.mem_of_mem_erase hv)
      exact Finset.sum_nonneg hnonneg
    have hsum_pos :
        0 < diff v0 + (Finset.univ.erase v0 : Finset V).sum fun v : V => diff v :=
      add_pos_of_pos_of_nonneg hv0_pos hsum_rest_nonneg
    have hsum_eq :
        (Finset.univ.sum fun v : V => diff v) =
          diff v0 + (Finset.univ.erase v0 : Finset V).sum fun v : V => diff v := by
      have hv0_mem : v0 ∈ (Finset.univ : Finset V) := hv0
      have h :=
        Finset.sum_erase_add (s := (Finset.univ : Finset V))
          (a := v0) (f := fun v => diff v) hv0_mem
      -- sum_erase_add gives the same identity with terms swapped
      simpa [diff, hv0_mem, add_comm, add_left_comm, add_assoc] using h.symm
    have hsum_pos' : 0 < (Finset.univ.sum fun v : V => diff v) := by
      calc
        0 < diff v0 + (Finset.univ.erase v0 : Finset V).sum (fun v : V => diff v) :=
          hsum_pos
        _ = (Finset.univ.sum fun v : V => diff v) := by
          symm
          exact hsum_eq
    have hsum_pos'' :
        0 <
          (Finset.univ.sum fun v : V => scoreFun (rank (P.pref v) c)) -
            (Finset.univ.sum fun v : V => scoreFun (rank (P.pref v) d)) :=
      by
      simpa [diff, Finset.sum_sub_distrib] using hsum_pos'
    exact sub_pos.mp hsum_pos''
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  let scoreSet : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate P scoreFun c))
  let maxScore : Int :=
    scoreSet.max' (hA.image _)
  have hle_max : scoreCandidate P scoreFun c ≤ maxScore := by
    have hmem : scoreCandidate P scoreFun c ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    exact Finset.le_max' scoreSet _ hmem
  have hlt_max : scoreCandidate P scoreFun d < maxScore :=
    lt_of_lt_of_le hlt hle_max
  have hd' : scoreCandidate P scoreFun d = maxScore := by
    have hd' : d ∈ scoringWinners P scoreFun := by
      simpa [scoringRule, scoreFun] using hd
    simpa [scoringWinners, hA, scoreSet, maxScore] using hd'
  exact (ne_of_lt hlt_max) hd'

end SocialChoice
