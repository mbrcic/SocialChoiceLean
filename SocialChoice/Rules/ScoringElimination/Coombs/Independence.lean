import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common
import SocialChoice.Axioms.Independence

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A]

private lemma scoreCandidate_veto_eq_zero_of_universal_bottom
    [DecidableEq A] (P : Profile V A) (d : A) (hbottom : ∀ v, BottomRank P v d) :
    scoreCandidate P (fun r => vetoScore (Fintype.card A) r) d = 0 := by
  classical
  have hscore :
      scoreCandidate P (fun r => vetoScore (Fintype.card A) r) d =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
    simpa [vetoScore] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := d))
  have hfilter :
      (Finset.univ.filter (fun v => ¬ BottomRank P v d)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact (Finset.mem_filter.mp hv).2 (hbottom v)
  simp [hscore, hfilter]

private lemma scoreCandidate_veto_eq_card_of_not_bottom
    [DecidableEq A] (P : Profile V A) (a : A) (hnot : ∀ v, ¬ BottomRank P v a) :
    scoreCandidate P (fun r => vetoScore (Fintype.card A) r) a = (Fintype.card V : Int) := by
  classical
  have hscore :
      scoreCandidate P (fun r => vetoScore (Fintype.card A) r) a =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v a)).card : Int) := by
    simpa [vetoScore] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := a))
  have hfilter :
      (Finset.univ.filter (fun v => ¬ BottomRank P v a)) = (Finset.univ : Finset V) := by
    apply Finset.ext
    intro v
    simp [hnot v]
  simp [hscore, hfilter]

private lemma lowestScoring_eq_singleton_of_universal_bottom
    [DecidableEq A] [Nonempty V]
    (P : Profile V A) (c d : A) (hcd : c ≠ d) (hbottom : ∀ v, BottomRank P v d) :
    lowestScoring P (fun r => vetoScore (Fintype.card A) r) = {d} := by
  classical
  let scoreVec : Nat → Int := fun r => vetoScore (Fintype.card A) r
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  have hscore_d : scoreCandidate P scoreVec d = 0 := by
    simpa [scoreVec] using
      (scoreCandidate_veto_eq_zero_of_universal_bottom (P := P) (d := d) hbottom)
  have hscore_other : ∀ a : A, a ≠ d →
      scoreCandidate P scoreVec a = (Fintype.card V : Int) := by
    intro a had
    have hnot : ∀ v, ¬ BottomRank P v a := by
      intro v
      exact (bottomRank_imp_not_bottomRank (P := P) (hcd := had.symm) (v := v) (hbottom v))
    simpa [scoreVec] using
      (scoreCandidate_veto_eq_card_of_not_bottom (P := P) (a := a) hnot)
  have hpos : (0 : Int) < (Fintype.card V : Int) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty V))
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have hle :=
      (lowestScoring_iff_forall_le (P := P) (score := scoreVec) (hA := hA) (c := a)).1 ha
    by_cases had : a = d
    · subst a
      simp
    · have hscore_a := hscore_other a had
      have hle' : (Fintype.card V : Int) ≤ 0 := by
        simpa [hscore_a, hscore_d] using (hle d)
      exact (False.elim ((not_lt_of_ge hle') (by simpa using hpos)))
  · intro ha
    have had : a = d := by
      simpa using (Finset.mem_singleton.mp ha)
    subst a
    apply (lowestScoring_iff_forall_le (P := P) (score := scoreVec) (hA := hA) (c := d)).2
    intro e
    by_cases hed : e = d
    · subst hed
      simp [hscore_d]
    · have hscore_e := hscore_other e hed
      simp [hscore_d, hscore_e]

theorem coombs_independenceOfUniversallyLeastPreferred :
    IndependenceOfUniversallyLeastPreferred coombs := by
  intro V A _ _ _ _ P c d hcd hbottom
  classical
  have hcard : ¬ Fintype.card A ≤ 1 := by
    intro hle
    have hsub : Subsingleton A :=
      (Fintype.card_le_one_iff_subsingleton).1 hle
    exact hcd (Subsingleton.elim _ _)
  let scoreVec : Nat → Int := fun r => vetoScore (Fintype.card A) r
  let L : Finset A := lowestScoring P scoreVec
  have hL : L = {d} := by
    simpa [L, scoreVec] using
      (lowestScoring_eq_singleton_of_universal_bottom (P := P) (c := c) (d := d) hcd hbottom)
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := P) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore A P =
        L.biUnion (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
    simpa [L, scoreVec] using haux
  have hcoombs_aux :
      scoringEliminationAux vetoScore A P =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
    calc
      scoringEliminationAux vetoScore A P =
          L.biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := haux'
      _ = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
        apply Finset.ext
        intro a
        constructor
        · intro ha
          rcases Finset.mem_biUnion.mp ha with ⟨c', hc', ha'⟩
          have hc'd : c' = d := by
            have hc'' : c' ∈ ({d} : Finset A) := by
              simpa [hL] using hc'
            simpa using (Finset.mem_singleton.mp hc'')
          subst hc'd
          simpa using ha'
        · intro ha
          apply Finset.mem_biUnion.mpr
          refine ⟨d, ?_, ?_⟩
          · simp [hL]
          · simpa using ha
  have hcoombs :
      coombs P = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
    classical
    have hcongr :
        @scoringEliminationAux V _ vetoScore A _ (fun a b => Classical.propDecidable (a = b)) P =
          @scoringEliminationAux V _ vetoScore A _ (inferInstance : DecidableEq A) P := by
      simpa using
        (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := P)
          (inst1 := fun a b => Classical.propDecidable (a = b))
          (inst2 := (inferInstance : DecidableEq A)))
    calc
      coombs P =
          @scoringEliminationAux V _ vetoScore A _ (fun a b => Classical.propDecidable (a = b)) P := by
        simp [coombs, scoringEliminationRule]
      _ =
          @scoringEliminationAux V _ vetoScore A _ (inferInstance : DecidableEq A) P := by
        simpa using hcongr
      _ = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
        simpa using hcoombs_aux
  classical
  let P' := restrictCandidates P (fun a => a ≠ d)
  have hcongr' :
      @scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (fun x y =>
        Classical.propDecidable (x = y)) P' =
        @scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (inferInstance :
          DecidableEq {x // x ≠ d}) P' := by
    simpa using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := P')
        (inst1 := fun x y => Classical.propDecidable (x = y))
        (inst2 := (inferInstance : DecidableEq {x // x ≠ d})))
  calc
    liftWinners (coombs (restrictCandidates P (fun a => a ≠ d))) =
        liftWinners (@scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (fun x y =>
          Classical.propDecidable (x = y)) P') := by
          simp [coombs, scoringEliminationRule, P']
    _ =
        liftWinners (@scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (inferInstance :
          DecidableEq {x // x ≠ d}) P') := by
          simp [hcongr']
    _ =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
          classical
          simp [liftWinners, liftFinset, restrictProfile, P']
          have hinst :
              (fun a b => Classical.propDecidable (a = b)) =
                (inferInstance : DecidableEq A) := by
            funext a b
            apply Subsingleton.elim
          cases hinst
          rfl
    _ = coombs P := by
          symm
          exact hcoombs

end SocialChoice
