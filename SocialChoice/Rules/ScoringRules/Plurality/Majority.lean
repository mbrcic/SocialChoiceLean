import SocialChoice.Axioms.Majority
import SocialChoice.Examples
import SocialChoice.Rules
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import Mathlib.Tactic.FinCases

namespace SocialChoice

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
    · simp [hne]
    · have hlt' := hlt d hne
      exact (by
        have : False := (not_lt_of_ge hcd) hlt'
        exact this.elim)
  · intro hd
    have hd' : d = c := by simpa using hd
    have hmax : ∀ e : A, topCount P e ≤ topCount P c := by
      intro e
      by_cases hne : e = c
      · simp [hne]
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

end SocialChoice

namespace SocialChoice

open Finset

private def listBallot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

private def pluralityMajorityLoserBallots : Fin 7 → ListBallot 3
  | 0 => Examples.listBallot012
  | 1 => Examples.listBallot012
  | 2 => Examples.listBallot012
  | 3 => Examples.listBallot120
  | 4 => Examples.listBallot120
  | 5 => listBallot210
  | 6 => listBallot210

private noncomputable def pluralityMajorityLoserProfile : Profile (Fin 7) (Fin 3) :=
  profileOfListBallots pluralityMajorityLoserBallots

private lemma bottomRank_iff_prefersInList {m n : ℕ} (ballots : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (ballots v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).2 (h d hd)

private lemma pluralityMajorityLoser_votersBottom :
    votersBottom pluralityMajorityLoserProfile 0 =
      ({3, 4, 5, 6} : Finset (Fin 7)) := by
  classical
  ext v
  fin_cases v <;>
    simp [pluralityMajorityLoserProfile, pluralityMajorityLoserBallots, votersBottom,
      bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma pluralityMajorityLoser_votersBottom_card :
    (votersBottom pluralityMajorityLoserProfile 0).card = 4 := by
  simp [pluralityMajorityLoser_votersBottom]

private lemma strictMajority_fin7 {S : Finset (Fin 7)} (hcard : S.card = 4) :
    StrictMajority S := by
  unfold StrictMajority
  simp [hcard]

private lemma pluralityMajorityLoser_strictMajority_bottom0 :
    StrictMajority (votersBottom pluralityMajorityLoserProfile 0) := by
  have hcard : (votersBottom pluralityMajorityLoserProfile 0).card = 4 :=
    pluralityMajorityLoser_votersBottom_card
  exact strictMajority_fin7 hcard

private lemma pluralityMajorityLoser_topCount0 : topCount pluralityMajorityLoserProfile 0 = 3 := by
  have hcount : countTop (fun v => (pluralityMajorityLoserBallots v).ranking) 0 = 3 := rfl
  have hcard : (votersTop pluralityMajorityLoserProfile 0).card = 3 := by
    simpa [pluralityMajorityLoserProfile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma pluralityMajorityLoser_topCount1 : topCount pluralityMajorityLoserProfile 1 = 2 := by
  have hcount : countTop (fun v => (pluralityMajorityLoserBallots v).ranking) 1 = 2 := rfl
  have hcard : (votersTop pluralityMajorityLoserProfile 1).card = 2 := by
    simpa [pluralityMajorityLoserProfile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma pluralityMajorityLoser_topCount2 : topCount pluralityMajorityLoserProfile 2 = 2 := by
  have hcount : countTop (fun v => (pluralityMajorityLoserBallots v).ranking) 2 = 2 := rfl
  have hcard : (votersTop pluralityMajorityLoserProfile 2).card = 2 := by
    simpa [pluralityMajorityLoserProfile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma pluralityMajorityLoser_topCount_le (d : Fin 3) :
    topCount pluralityMajorityLoserProfile d ≤ topCount pluralityMajorityLoserProfile 0 := by
  fin_cases d <;>
    simp [pluralityMajorityLoser_topCount0, pluralityMajorityLoser_topCount1,
      pluralityMajorityLoser_topCount2]

private lemma pluralityMajorityLoser_has_a :
    (0 : Fin 3) ∈ plurality pluralityMajorityLoserProfile := by
  classical
  have hmax :
      ∀ d : Fin 3,
        topCount pluralityMajorityLoserProfile d ≤ topCount pluralityMajorityLoserProfile 0 := by
    intro d
    exact pluralityMajorityLoser_topCount_le d
  have hmem :
      (0 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3,
            topCount pluralityMajorityLoserProfile d ≤ topCount pluralityMajorityLoserProfile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

theorem plurality_not_majorityLoserCriterion : ¬ MajorityLoserCriterion plurality := by
  intro hmaj
  have hmaj' : StrictMajority (votersBottom pluralityMajorityLoserProfile 0) :=
    pluralityMajorityLoser_strictMajority_bottom0
  have hne : ∃ d : Fin 3, d ≠ 0 := by
    exact ⟨1, by decide⟩
  have hforbid : (0 : Fin 3) ∉ plurality pluralityMajorityLoserProfile :=
    hmaj pluralityMajorityLoserProfile 0 hmaj' hne
  have hwinner : (0 : Fin 3) ∈ plurality pluralityMajorityLoserProfile :=
    pluralityMajorityLoser_has_a
  exact hforbid hwinner

end SocialChoice
