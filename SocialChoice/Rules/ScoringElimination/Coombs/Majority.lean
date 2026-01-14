import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Majority
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset

lemma rank_eq_card_sub_one_iff_bottomRank
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (v : V) (c : A) :
    rank (P.pref v) c = Fintype.card A - 1 ↔ BottomRank P v c := by
  classical
  let r := P.pref v
  have hsubset : (Finset.univ.filter (fun d => r.lt d c)) ⊆ (Finset.univ.erase c) := by
    intro d hd
    have hd' : r.lt d c := (Finset.mem_filter.mp hd).2
    have hdc : d ≠ c := by
      intro hdc
      subst hdc
      exact lt_irrefl _ hd'
    exact Finset.mem_erase.mpr ⟨hdc, by simp⟩
  constructor
  · intro hrank d hdc
    have hcard :
        (Finset.univ.filter (fun d => r.lt d c)).card =
          (Finset.univ.erase c).card := by
      simpa [rank] using hrank
    have hEq : (Finset.univ.filter (fun d => r.lt d c)) = (Finset.univ.erase c) := by
      apply Finset.eq_of_subset_of_card_le hsubset
      simp [hcard]
    have hdmem : d ∈ (Finset.univ.erase c) := by
      exact Finset.mem_erase.mpr ⟨hdc, by simp⟩
    have hdmem' : d ∈ (Finset.univ.filter (fun d => r.lt d c)) := by
      simpa [hEq] using hdmem
    exact (Finset.mem_filter.mp hdmem').2
  · intro hbottom
    have hEq : (Finset.univ.filter (fun d => r.lt d c)) = (Finset.univ.erase c) := by
      ext d
      constructor
      · intro hd
        have hd' : r.lt d c := (Finset.mem_filter.mp hd).2
        have hdc : d ≠ c := by
          intro hdc
          subst hdc
          exact lt_irrefl _ hd'
        exact Finset.mem_erase.mpr ⟨hdc, by simp⟩
      · intro hd
        have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
        have hlt : r.lt d c := hbottom d hdc
        exact Finset.mem_filter.mpr ⟨by simp, hlt⟩
    simp [rank, hEq]

lemma vetoScore_scoreCandidate_eq_notBottom_card
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A)
    [DecidablePred (fun v => BottomRank P v c)]
    [DecidablePred (fun v => ¬ BottomRank P v c)] :
    scoreCandidate P (fun r => if r = Fintype.card A - 1 then 0 else 1) c =
      ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
  have hrank : ∀ v, (rank (P.pref v) c = Fintype.card A - 1) ↔ BottomRank P v c := by
    intro v
    simpa using (rank_eq_card_sub_one_iff_bottomRank (P := P) (v := v) (c := c))
  have heq :
      (∑ v : V, (fun r => if r = Fintype.card A - 1 then (0 : Int) else 1) (rank (P.pref v) c)) =
        ∑ v : V, if BottomRank P v c then (0 : Int) else 1 := by
    apply Finset.sum_congr rfl
    intro v _
    simp [hrank v]
  have hsum :
      (∑ v : V, if BottomRank P v c then (0 : Int) else 1) =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
    have hsum' :
        (∑ v : V, if BottomRank P v c then (0 : Int) else 1) =
          (Finset.univ.filter (fun v => ¬ BottomRank P v c)).sum (fun _ => (1 : Int)) := by
      have h :=
        (Finset.sum_filter (s := (Finset.univ : Finset V))
          (p := fun v => ¬ BottomRank P v c)
          (f := fun _ => (1 : Int)))
      have h' :
          (∑ v : V, if BottomRank P v c then (0 : Int) else 1) =
            ∑ v : V, if ¬ BottomRank P v c then (1 : Int) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hbc : BottomRank P v c
        · simp [hbc]
        · simp [hbc]
      exact h'.trans h.symm
    have hsum'' :
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).sum (fun _ => (1 : Int)) =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
      simp
    exact hsum'.trans hsum''
  have hscore : scoreCandidate P (fun r => if r = Fintype.card A - 1 then 0 else 1) c =
      ∑ v : V, if BottomRank P v c then (0 : Int) else 1 := by
    simpa [scoreCandidate] using heq
  calc
    scoreCandidate P (fun r => if r = Fintype.card A - 1 then 0 else 1) c
        = ∑ v : V, if BottomRank P v c then (0 : Int) else 1 := hscore
    _ = ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := hsum

lemma bottomRank_imp_not_bottomRank
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {c d : A} (hcd : c ≠ d) (v : V) :
    BottomRank P v c → ¬ BottomRank P v d := by
  intro hbc hbd
  have hdc : Prefers P v d c := hbc d hcd.symm
  have hcd' : Prefers P v c d := hbd c (by simpa [eq_comm] using hcd)
  let _ : Preorder A := (P.pref v).toPreorder
  exact lt_asymm hcd' hdc

theorem coombs_majorityLoserCriterion : MajorityLoserCriterion coombs := by
  intro V A _ _ P c hmaj hne
  classical
  rcases hne with ⟨d0, hd0c⟩
  haveI : Nonempty A := ⟨d0⟩
  let m := Fintype.card A
  let scoreVec : Nat → Int := fun r => vetoScore m r
  let L : Finset A := lowestScoring P scoreVec
  have hcard : ¬ Fintype.card A ≤ 1 := by
    intro hle
    have hsub : ∀ a b : A, a = b := (Fintype.card_le_one_iff.mp hle)
    exact hd0c (hsub d0 c)
  have hnotbottom_c_eq :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        Fintype.card V - (votersBottom P c).card := by
    have hsum :
        (Finset.univ.filter (fun v => BottomRank P v c)).card +
          (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
          (Finset.univ : Finset V).card := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset V)) (p := fun v => BottomRank P v c))
    have hsum' :
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
          (Finset.univ : Finset V).card -
            (Finset.univ.filter (fun v => BottomRank P v c)).card := by
      apply Nat.eq_sub_of_add_eq
      simpa [add_comm] using hsum
    simpa [votersBottom] using hsum'
  have hmaj' : 2 * (votersBottom P c).card > Fintype.card V := by
    simpa [StrictMajority] using hmaj
  have hlt_nat :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card <
        (votersBottom P c).card := by
    have hlt_nat' : Fintype.card V - (votersBottom P c).card < (votersBottom P c).card := by
      omega
    simpa [hnotbottom_c_eq] using hlt_nat'
  have hscore_lt : ∀ d : A, d ≠ c →
      scoreCandidate P scoreVec c < scoreCandidate P scoreVec d := by
    intro d hdc
    have hnotbottom_d_ge :
        (votersBottom P c).card ≤
          (Finset.univ.filter (fun v => ¬ BottomRank P v d)).card := by
      have hsubset : ∀ v, BottomRank P v c → ¬ BottomRank P v d := by
        intro v hbc
        exact bottomRank_imp_not_bottomRank (P := P) (c := c) (d := d) hdc.symm v hbc
      have hcard :=
        cardinality_lemma (p := fun v => BottomRank P v c)
          (q := fun v => ¬ BottomRank P v d) hsubset
      simpa [votersBottom] using hcard
    have hscore_c :
        scoreCandidate P scoreVec c =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
      simpa [scoreVec, vetoScore] using
        (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := c))
    have hscore_d :
        scoreCandidate P scoreVec d =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
      simpa [scoreVec, vetoScore] using
        (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := d))
    have hlt_int :
        ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) <
          ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
      have hlt_int' :
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) <
            ((votersBottom P c).card : Int) := by
        exact_mod_cast hlt_nat
      have hle_int :
          ((votersBottom P c).card : Int) ≤
            ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
        exact_mod_cast hnotbottom_d_ge
      exact lt_of_lt_of_le hlt_int' hle_int
    simpa [hscore_c, hscore_d] using hlt_int
  have hL_subset : L ⊆ ({c} : Finset A) := by
    intro d hd
    by_cases hdc : d = c
    · simp [hdc]
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := P) (score := scoreVec) (c := d) (e := c) hd
      have hlt := hscore_lt d hdc
      exact (False.elim ((not_lt_of_ge hle) hlt))
  have hLne : L.Nonempty := by
    apply lowestScoring_nonempty
    exact (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
  have hc_low : c ∈ L := by
    rcases hLne with ⟨d, hd⟩
    have hd' : d = c := by
      have : d ∈ ({c} : Finset A) := hL_subset hd
      simpa using this
    simpa [hd'] using hd
  have hL_eq : L = {c} := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have : d ∈ ({c} : Finset A) := hL_subset hd
      simpa using this
    · intro hd
      have hd' : d = c := by simpa using hd
      simpa [hd'] using hc_low
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := P) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore A P =
        L.biUnion (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
    simpa [m, scoreVec, L] using haux
  have haux'' :
      scoringEliminationAux vetoScore A P =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c)) := by
    simpa [hL_eq, L] using haux'
  have hnot :
      c ∉ scoringEliminationAux vetoScore A P := by
    have hnot' :
        c ∉ liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c)) :=
      not_mem_liftFinset_removed (s := scoringEliminationAux vetoScore _ (restrictProfile P c))
    simpa [haux''] using hnot'
  simpa [coombs, scoringEliminationRule] using hnot

end SocialChoice
