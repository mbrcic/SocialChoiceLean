import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Axiomdb.FintypeApproach.Axioms
import Axiomdb.FintypeApproach.Rules

namespace FintypeApproach

open Finset

-- Plurality satisfies the majority criterion.
theorem plurality_majorityCriterion : MajorityCriterion plurality := by
  intro V A _ _ P c hmaj
  classical
  -- A strict majority for c implies every other candidate has fewer top votes.
  have hlt : ∀ d : A, d ≠ c → topCount P d < topCount P c := by
    intro d hne
    have hdisj : Disjoint (votersTop P c) (votersTop P d) := by
      refine disjoint_left.2 ?_
      intro v hv1 hv2
      have hc : TopRank P v c := (mem_filter.mp hv1).2
      have hd : TopRank P v d := (mem_filter.mp hv2).2
      have hcd : Prefers P v c d := hc d hne
      have hdc : Prefers P v d c := hd c (by simpa [eq_comm] using hne)
      have hcontra : ¬ (P.pref v).lt d c := by
        let _ : Preorder A := (P.pref v).toPreorder
        exact (lt_asymm (a := c) (b := d) hcd)
      exact hcontra hdc
    have hsubset : votersTop P c ∪ votersTop P d ⊆ (Finset.univ : Finset V) := by
      intro v hv
      exact mem_univ v
    have hcard : (votersTop P c ∪ votersTop P d).card ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card hsubset
    have hsum : topCount P c + topCount P d ≤ Fintype.card V := by
      have hcard' :
          (votersTop P c ∪ votersTop P d).card =
            (votersTop P c).card + (votersTop P d).card := by
        simpa using
          (Finset.card_union_of_disjoint (s := votersTop P c) (t := votersTop P d) hdisj)
      have hcard'' :
          (votersTop P c).card + (votersTop P d).card ≤ (Finset.univ : Finset V).card := by
        simpa [hcard'] using hcard
      simpa [topCount, Finset.card_univ] using hcard''
    have hmaj' : Fintype.card V < 2 * topCount P c := by
      simpa [StrictMajority, topCount] using hmaj
    have hlt' : topCount P c + topCount P d < 2 * topCount P c :=
      lt_of_le_of_lt hsum hmaj'
    have hlt'' : topCount P c + topCount P d < topCount P c + topCount P c := by
      simpa [Nat.two_mul] using hlt'
    exact Nat.lt_of_add_lt_add_left hlt''
  -- Show the plurality winners are exactly {c}.
  apply Finset.ext
  intro d
  constructor
  · intro hd
    have hd' : ∀ e : A, topCount P e ≤ topCount P d := by
      have hd' : d ∈ (Finset.univ.filter
          (fun c => ∀ e : A, topCount P e ≤ topCount P c)) := by
        simpa [plurality] using hd
      exact (mem_filter.mp hd').2
    have hcd : topCount P c ≤ topCount P d := hd' c
    by_cases hne : d = c
    · simpa [hne]
    · have hlt' := hlt d hne
      exact (by
        have : False := (not_lt_of_ge hcd) hlt'
        simpa [hne] using this)
  · intro hd
    have hd' : d = c := by simpa using hd
    have hmax : ∀ e : A, topCount P e ≤ topCount P c := by
      intro e
      by_cases hne : e = c
      · simpa [hne]
      · exact Nat.le_of_lt (hlt e hne)
    have hc : c ∈ (Finset.univ : Finset A) := by
      exact mem_univ c
    have hc' :
        c ∈ (Finset.univ.filter
          (fun c => ∀ e : A, topCount P e ≤ topCount P c)) := by
      exact mem_filter.mpr ⟨hc, hmax⟩
    have hc'' : c ∈ plurality P := by
      simpa [plurality] using hc'
    simpa [hd'] using hc''

-- Borda is anonymous.
theorem borda_anonymous : Anonymity borda := by
  intro V A _ _ P σ
  classical
  have score_perm :
      ∀ (score : Nat → Int) (c : A),
        scoreCandidate (permuteVoters P σ) score c = scoreCandidate P score c := by
    intro score c
    unfold scoreCandidate
    refine Finset.sum_equiv (s := (Finset.univ : Finset V))
      (t := (Finset.univ : Finset V)) (e := σ) ?_ ?_
    · intro v
      simp
    · intro v hv
      simp [permuteVoters, rank]
  unfold borda scoringRule
  by_cases h : (Finset.univ : Finset A).Nonempty
  · simp [scoringWinners, h, score_perm]
  · simp [scoringWinners, h]

-- Borda violates the majority criterion.
theorem borda_not_majorityCriterion : ¬ MajorityCriterion borda := by
  intro hmaj
  let ballotABC : LinearOrder (Fin 3) := inferInstance
  let rankBCA : Fin 3 → Nat :=
    fun c => if c = 1 then 0 else if c = 2 then 1 else 2
  have rankBCA_inj : Function.Injective rankBCA := by
    classical
    decide
  let ballotBCA : LinearOrder (Fin 3) := LinearOrder.lift' rankBCA rankBCA_inj
  let P : Profile (Fin 3) (Fin 3) :=
    { pref := fun v => if v = 0 ∨ v = 1 then ballotABC else ballotBCA }
  have htop0 : TopRank P 0 (0 : Fin 3) := by
    intro d hne
    fin_cases d <;> simp [P, ballotABC, Prefers] at hne ⊢
  have htop1 : TopRank P 1 (0 : Fin 3) := by
    intro d hne
    fin_cases d <;> simp [P, ballotABC, Prefers] at hne ⊢
  have htop2 : ¬ TopRank P 2 (0 : Fin 3) := by
    intro h
    have hv : ¬ ((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) := by decide
    have h' : ballotBCA.lt (0 : Fin 3) (1 : Fin 3) := by
      simpa [P, Prefers, hv] using (h (1 : Fin 3) (by decide))
    have h'' : rankBCA (0 : Fin 3) < rankBCA (1 : Fin 3) := by
      change ballotBCA.lt (0 : Fin 3) (1 : Fin 3)
      exact h'
    have h0 : rankBCA (0 : Fin 3) = 2 := rfl
    have h1 : rankBCA (1 : Fin 3) = 0 := rfl
    have hcontra : ¬ (2 : Nat) < 0 := by decide
    have hcontra' : ¬ rankBCA (0 : Fin 3) < rankBCA (1 : Fin 3) := by
      simpa [h0, h1] using hcontra
    exact hcontra' h''
  have hvotersTop : votersTop P (0 : Fin 3) = ({0,1} : Finset (Fin 3)) := by
    ext v
    fin_cases v <;> simp [votersTop, htop0, htop1, htop2]
  have hmaj' : StrictMajority (votersTop P (0 : Fin 3)) := by
    have : StrictMajority ({0,1} : Finset (Fin 3)) := by decide
    simpa [hvotersTop] using this
  have hb : (1 : Fin 3) ∈ borda P := by
    decide
  have hres : borda P = {(0 : Fin 3)} := hmaj (V := Fin 3) (A := Fin 3) (P := P) (c := 0) hmaj'
  have hb' : (1 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := by
    simpa [hres] using hb
  have hne : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
  simpa [hne] using hb'

-- Plurality satisfies positive involvement.
theorem plurality_positiveInvolvement : PositiveInvolvement plurality := by
  intro V A _ _ P c ballot hc htop
  classical
  let P' := addVoter P ballot
  have ballot_not_top : ∀ d : A, d ≠ c → ¬ BallotTop ballot d := by
    intro d hne htopd
    have hcd : ballot.lt c d := htop d hne
    have hdc : ballot.lt d c := htopd c (by simpa [eq_comm] using hne)
    let _ : Preorder A := ballot.toPreorder
    exact (lt_asymm (a := c) (b := d) hcd) hdc
  let rightTop : A → Finset Unit :=
    fun d => if BallotTop ballot d then {()} else ∅
  have votersTop_addVoter :
      ∀ d : A, votersTop P' d = (votersTop P d).disjSum (rightTop d) := by
    intro d
    ext v
    cases v with
    | inl v =>
        simp [votersTop, P', addVoter, TopRank, Prefers, rightTop, Finset.inl_mem_disjSum]
    | inr u =>
        cases u
        have hL : Sum.inr PUnit.unit ∈ votersTop P' d ↔ BallotTop ballot d := by
          simp [votersTop, P', addVoter, TopRank, Prefers, BallotTop]
        by_cases hbt : BallotTop ballot d
        · simp [hL, rightTop, hbt, Finset.inr_mem_disjSum]
        · simp [hL, rightTop, hbt, Finset.inr_mem_disjSum]
  have topCount_addVoter :
      ∀ d : A, topCount P' d = topCount P d + (rightTop d).card := by
    intro d
    unfold topCount
    simp [votersTop_addVoter, Finset.card_disjSum]
  have topCount_c : topCount P' c = topCount P c + 1 := by
    have : rightTop c = {()} := by
      simp [rightTop, htop]
    simpa [this] using topCount_addVoter c
  have topCount_ne : ∀ d : A, d ≠ c → topCount P' d = topCount P d := by
    intro d hne
    have : rightTop d = ∅ := by
      simp [rightTop, ballot_not_top d hne]
    simpa [this] using topCount_addVoter d
  have hmax_old : ∀ d : A, topCount P d ≤ topCount P c := by
    have hc' : c ∈ (Finset.univ.filter
        (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
      simpa [plurality] using hc
    exact (mem_filter.mp hc').2
  have hmax_new : ∀ d : A, topCount P' d ≤ topCount P' c := by
    intro d
    by_cases hne : d = c
    · simp [hne]
    · calc
        topCount P' d = topCount P d := topCount_ne d hne
        _ ≤ topCount P c := hmax_old d
        _ ≤ topCount P c + 1 := Nat.le_succ _
        _ = topCount P' c := topCount_c.symm
  have hc' : c ∈ (Finset.univ.filter
      (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) := by
    exact mem_filter.mpr ⟨mem_univ _, hmax_new⟩
  simpa [plurality] using hc'

end FintypeApproach
