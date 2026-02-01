import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SocialChoice.Axioms.Pareto
import SocialChoice.Rules.ScoringElimination.Basic

namespace SocialChoice

open Finset

lemma scoreCandidate_lt_of_prefers
    (score : Nat → Nat → Int) (hstrict : strictlyDecreasingScore score)
    {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d) :
    scoreCandidate P (fun r => score (Fintype.card A) r) d <
      scoreCandidate P (fun r => score (Fintype.card A) r) c := by
  classical
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
  unfold scoreCandidate
  refine Finset.sum_lt_sum ?_ ?_
  · intro v hv
    have hlt_rank : rank (P.pref v) c < rank (P.pref v) d :=
      rank_lt_of_lt (r := P.pref v) (c := c) (d := d) (hpref v)
    have hlt_score :
        scoreFun (rank (P.pref v) d) < scoreFun (rank (P.pref v) c) :=
      hstrict (Fintype.card A) _ _ hlt_rank
        (rank_lt_card (P.pref v) c) (rank_lt_card (P.pref v) d)
    exact hlt_score.le
  · rcases Classical.choice (inferInstance : Nonempty V) with v0
    refine ⟨v0, by simp, ?_⟩
    have hlt_rank : rank (P.pref v0) c < rank (P.pref v0) d :=
      rank_lt_of_lt (r := P.pref v0) (c := c) (d := d) (hpref v0)
    exact hstrict (Fintype.card A) _ _ hlt_rank
      (rank_lt_card (P.pref v0) c) (rank_lt_card (P.pref v0) d)

theorem scoringEliminationRule_paretoEfficiency
    (score : Nat → Nat → Int) (hstrict : strictlyDecreasingScore score) :
    ParetoEfficiency (scoringEliminationRule score) := by
  intro V A _ _ _ P c d hpref
  classical
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A']
      {V' : Type} [Fintype V'] [Nonempty V']
      (P' : Profile V' A') (c d : A'),
        Fintype.card A' = k →
        (∀ v : V', Prefers P' v c d) →
          d ∉ scoringEliminationAux score A' P'
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ V' _ _ P' c d hk hpref
    by_cases hle : Fintype.card A' ≤ 1
    · have hsub : Subsingleton A' :=
        (Fintype.card_le_one_iff_subsingleton).1 hle
      have hcd : c = d := Subsingleton.elim _ _
      rcases Classical.choice (inferInstance : Nonempty V') with v0
      have hpref0 : Prefers P' v0 c d := hpref v0
      subst hcd
      have hfalse : False := by
        let _ := P'.pref v0
        exact (lt_irrefl _ hpref0)
      exact hfalse.elim
    · let m := Fintype.card A'
      let scoreVec : Nat → Int := fun r => score m r
      have hlt :
          scoreCandidate P' scoreVec d < scoreCandidate P' scoreVec c :=
        scoreCandidate_lt_of_prefers (score := score) (hstrict := hstrict)
          (P := P') (c := c) (d := d) hpref
      have hnotc : c ∉ lowestScoring P' scoreVec := by
        intro hc
        have hle' :=
          scoreCandidate_le_of_mem_lowestScoring
            (P := P') (score := scoreVec) (c := c) (e := d) hc
        exact (not_lt_of_ge hle') hlt
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := score) (P := P') (A := A') (hcard := hle)
      intro hd
      have hd' :
          d ∈ (lowestScoring P' scoreVec).biUnion
            (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P' c))) := by
        simpa [haux, m, scoreVec] using hd
      rcases Finset.mem_biUnion.mp hd' with ⟨ℓ, hℓL, hdmem⟩
      have hne_c : c ≠ ℓ := by
        intro hEq
        subst hEq
        exact hnotc hℓL
      rcases (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux score _ (restrictProfile P' ℓ)) (x := d)).1 hdmem
        with ⟨hdne, hdsub⟩
      have hpref' :
          ∀ v : V', Prefers (restrictProfile P' ℓ) v ⟨c, hne_c⟩ ⟨d, hdne⟩ := by
        intro v
        simpa using (hpref v)
      have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
        have hcard_sub_lt : Fintype.card {x : A' // x ≠ ℓ} < Fintype.card A' :=
          card_restrict_lt ℓ
        simpa [hk] using hcard_sub_lt
      have hrec :=
        ih (Fintype.card {x : A' // x ≠ ℓ}) hklt
          (A' := {x : A' // x ≠ ℓ}) (V' := V')
          (P' := restrictProfile P' ℓ)
          (c := ⟨c, hne_c⟩) (d := ⟨d, hdne⟩) (by rfl) hpref'
      exact hrec hdsub
  simpa [scoringEliminationRule, hn] using
    (hStrong (A' := A) (V' := V) (P' := P) (c := c) (d := d) (by rfl) hpref)

end SocialChoice
