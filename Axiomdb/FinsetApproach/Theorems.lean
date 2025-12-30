import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Axiomdb.FinsetApproach.Axioms
import Axiomdb.FinsetApproach.Rules

namespace FinsetApproach

open Finset

-- Plurality satisfies the majority criterion.
theorem plurality_majorityCriterion : MajorityCriterion plurality := by
  intro P c hmaj
  classical
  -- A strict majority for c implies every other candidate has fewer top votes.
  have hlt : ∀ d : Agenda P, d ≠ c → topCount P d < topCount P c := by
    intro d hne
    have hdisj : Disjoint (votersTop P c) (votersTop P d) := by
      refine disjoint_left.2 ?_
      intro v hv1 hv2
      have hc : TopRank P v c := (mem_filter.mp hv1).2
      have hd : TopRank P v d := (mem_filter.mp hv2).2
      have hcd : Prefers P v c d := hc d hne
      have hdc : Prefers P v d c := hd c (by simpa [eq_comm] using hne)
      have hcontra : ¬ (P.pref v).lt d c := by
        let _ : Preorder (Agenda P) := (P.pref v).toPreorder
        exact (lt_asymm (a := c) (b := d) hcd)
      exact hcontra hdc
    have hsubset : votersTop P c ∪ votersTop P d ⊆ P.voters.attach := by
      intro v hv
      rcases mem_union.mp hv with hv | hv
      · exact (mem_filter.mp hv).1
      · exact (mem_filter.mp hv).1
    have hcard : (votersTop P c ∪ votersTop P d).card ≤ P.voters.attach.card :=
      Finset.card_le_card hsubset
    have hsum : topCount P c + topCount P d ≤ P.voters.card := by
      have hcard' :
          (votersTop P c ∪ votersTop P d).card =
            (votersTop P c).card + (votersTop P d).card := by
        simpa using
          (Finset.card_union_of_disjoint (s := votersTop P c) (t := votersTop P d) hdisj)
      have hcard'' :
          (votersTop P c).card + (votersTop P d).card ≤ P.voters.attach.card := by
        simpa [hcard'] using hcard
      simpa [topCount, Finset.card_attach] using hcard''
    have hmaj' : P.voters.card < 2 * topCount P c := by
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
    have hd' : ∀ e : Agenda P, topCount P e ≤ topCount P d := by
      have hd' : d ∈ P.candidates.attach.filter
          (fun c => ∀ e : Agenda P, topCount P e ≤ topCount P c) := by
        simpa [plurality] using hd
      exact (mem_filter.mp hd').2
    have hcd : topCount P c ≤ topCount P d := hd' c
    by_cases hne : d = c
    · simp [hne]
    · have hlt' := hlt d hne
      have : False := (not_lt_of_ge hcd) hlt'
      exact (by simpa [hne] using this)
  · intro hd
    have hd' : d = c := by simpa using hd
    have hmax : ∀ e : Agenda P, topCount P e ≤ topCount P c := by
      intro e
      by_cases hne : e = c
      · simp [hne]
      · exact Nat.le_of_lt (hlt e hne)
    have hc : c ∈ P.candidates.attach := by
      simpa using (Finset.mem_attach (s := P.candidates) c)
    have hc' :
        c ∈ P.candidates.attach.filter
          (fun c => ∀ e : Agenda P, topCount P e ≤ topCount P c) := by
      exact mem_filter.mpr ⟨hc, hmax⟩
    have hc'' : c ∈ plurality P := by
      simpa [plurality] using hc'
    simpa [hd'] using hc''

-- Borda is anonymous.
theorem borda_anonymous : Anonymity borda := by
  intro P σ
  classical
  have score_perm :
      ∀ (score : Nat → Int) (c : Agenda P),
        scoreCandidate (permuteVoters P σ) score c = scoreCandidate P score c := by
    intro score c
    unfold scoreCandidate
    refine Finset.sum_equiv (s := P.voters.attach) (t := P.voters.attach) (e := σ) ?_ ?_
    · intro v
      constructor <;> intro _ <;> exact Finset.mem_attach (s := P.voters) _
    · intro v hv
      simp [permuteVoters, rank]
  unfold borda scoringRule
  by_cases h : P.candidates.Nonempty
  · have h' : (permuteVoters P σ).candidates.Nonempty := by
      simpa using h
    simp [scoringWinners, h, h', score_perm]
    simp [permuteVoters]
  · have h' : ¬ (permuteVoters P σ).candidates.Nonempty := by
      simpa using h
    simp [scoringWinners, h, h']

-- Borda violates the majority criterion.
theorem borda_not_majorityCriterion : ¬ MajorityCriterion borda := by
  intro hmaj
  let voters : Finset Voter := {0,1,2}
  let candidates : Finset Cand := {0,1,2}
  let ballotABC : LinearOrder {a // a ∈ candidates} := inferInstance
  let rankBCA : {a // a ∈ candidates} → Nat :=
    fun a => if a.1 = 1 then 0 else if a.1 = 2 then 1 else 2
  have rankBCA_inj : Function.Injective rankBCA := by
    classical
    decide
  let ballotBCA : LinearOrder {a // a ∈ candidates} := LinearOrder.lift' rankBCA rankBCA_inj
  let P : Profile :=
    { voters := voters
      candidates := candidates
      pref := fun v => if v.1 = 0 ∨ v.1 = 1 then ballotABC else ballotBCA }
  have h0c : (0 : Cand) ∈ P.candidates := by
    simp [P, candidates]
  have h1c : (1 : Cand) ∈ P.candidates := by
    simp [P, candidates]
  let a : Agenda P := ⟨0, h0c⟩
  let b : Agenda P := ⟨1, h1c⟩
  have htop0 : TopRank P ⟨0, by simpa [P, voters]⟩ a := by
    intro d hne
    have hd : d.1 = 0 ∨ d.1 = 1 ∨ d.1 = 2 := by
      have : d.1 ∈ P.candidates := d.2
      simpa [P, candidates] using this
    rcases hd with hd | hd | hd
    · cases hne (by ext; simpa [a, hd])
    · simp [P, ballotABC, Prefers, a, hd]
    · simp [P, ballotABC, Prefers, a, hd]
  have htop1 : TopRank P ⟨1, by simpa [P, voters]⟩ a := by
    intro d hne
    have hd : d.1 = 0 ∨ d.1 = 1 ∨ d.1 = 2 := by
      have : d.1 ∈ P.candidates := d.2
      simpa [P, candidates] using this
    rcases hd with hd | hd | hd
    · cases hne (by ext; simpa [a, hd])
    · simp [P, ballotABC, Prefers, a, hd]
    · simp [P, ballotABC, Prefers, a, hd]
  have htop2 : ¬ TopRank P ⟨2, by simpa [P, voters]⟩ a := by
    intro h
    have hv : ¬ ((2 : Voter) = 0 ∨ (2 : Voter) = 1) := by decide
    have h' : ballotBCA.lt a b := by
      simpa [P, Prefers, hv] using (h b (by
        intro hEq
        cases hEq
        simp at h1c))
    have h'' : rankBCA a < rankBCA b := by
      change ballotBCA.lt a b
      exact h'
    have h0 : rankBCA a = 2 := rfl
    have h1 : rankBCA b = 0 := rfl
    have hcontra : ¬ (2 : Nat) < 0 := by decide
    have hcontra' : ¬ rankBCA a < rankBCA b := by
      simpa [h0, h1] using hcontra
    exact hcontra' h''
  have hvotersTop : votersTop P a = {⟨0, by simpa [P, voters]⟩, ⟨1, by simpa [P, voters]⟩} := by
    ext v
    rcases v with ⟨v, hv⟩
    have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by
      have : v ∈ P.voters := hv
      simpa [P, voters] using this
    rcases hv' with hv' | hv' | hv'
    · subst hv'
      simp [votersTop, htop0]
    · subst hv'
      simp [votersTop, htop1]
    · subst hv'
      simp [votersTop, htop2]
  have hmaj' : StrictMajority P (votersTop P a) := by
    have : 2 * ({⟨0, by simpa [P, voters]⟩, ⟨1, by simpa [P, voters]⟩} :
        Finset (Electorate P)).card > P.voters.card := by decide
    simpa [StrictMajority, hvotersTop] using this
  have hb : b ∈ borda P := by
    decide
  have hres : borda P = {a} := hmaj (P := P) (c := a) hmaj'
  have hb' : b ∈ ({a} : Finset (Agenda P)) := by
    simpa [hres] using hb
  have hne : b ≠ a := by
    intro hEq
    cases hEq
    have : (1 : Cand) = 0 := by rfl
    simp at this
  simpa [hne] using hb'

-- Plurality satisfies positive involvement.
theorem plurality_positiveInvolvement : PositiveInvolvement plurality := by
  intro P c v hv ballot hc htop
  classical
  let P' := addVoter P v ballot
  let v0 : Electorate P' := ⟨v, mem_insert_self _ _⟩
  let incl : Electorate P → Electorate P' := fun w => ⟨w.1, mem_insert_of_mem w.2⟩
  have hincl : Function.Injective incl := by
    intro w₁ w₂ h
    cases w₁
    cases w₂
    cases h
    rfl
  have hne_old : ∀ w : Electorate P, (w.1 : Voter) ≠ v := by
    intro w h
    exact hv (by simpa [h] using w.2)
  have htop_old : ∀ (w : Electorate P) (d : Agenda P),
      TopRank P' (incl w) d ↔ TopRank P w d := by
    intro w d
    have hne : (w.1 : Voter) ≠ v := hne_old w
    simp [P', incl, addVoter, hne, TopRank, Prefers]
  have htop_new_c : TopRank P' v0 c := by
    intro d hne
    have : ballot.lt c d := htop d hne
    simpa [P', v0, addVoter, TopRank, Prefers] using this
  have htop_new_not : ∀ d : Agenda P, d ≠ c → ¬ TopRank P' v0 d := by
    intro d hne htopd
    have hcd : Prefers P' v0 c d := by
      have : ballot.lt c d := htop d hne
      simpa [P', v0, addVoter, Prefers] using this
    have hdc : Prefers P' v0 d c := htopd c (by simpa [eq_comm] using hne)
    have hcontra : ¬ (P'.pref v0).lt d c := by
      let _ : Preorder (Agenda P) := (P'.pref v0).toPreorder
      exact (lt_asymm (a := c) (b := d) hcd)
    exact hcontra hdc
  have hnot_mem_image : v0 ∉ (P.voters.attach.image incl) := by
    intro hmem
    rcases mem_image.mp hmem with ⟨w, hw, hw'⟩
    have hwval : (w : Voter) = v := by
      exact congrArg Subtype.val hw'
    exact hv (by simpa [hwval] using w.2)
  have topCount_addVoter_c : topCount P' c = topCount P c + 1 := by
    have hattach : P'.voters.attach =
        insert v0 ((P.voters.attach).image incl) := by
      simp [P', v0, incl, addVoter, Finset.attach_insert]
    have hfilter :
        (((P.voters.attach).image incl).filter (fun w => TopRank P' w c)) =
          ((P.voters.attach).filter (fun w => TopRank P w c)).image incl := by
      simpa [htop_old] using
        (Finset.filter_image (s := P.voters.attach) (f := incl) (p := fun w => TopRank P' w c))
    have hnot_mem_filter :
        v0 ∉ (((P.voters.attach).image incl).filter (fun w => TopRank P' w c)) := by
      intro hmem
      have hsubset :
          (((P.voters.attach).image incl).filter (fun w => TopRank P' w c)) ⊆
            (P.voters.attach).image incl := by
        exact filter_subset _ _
      exact hnot_mem_image (hsubset hmem)
    unfold topCount votersTop
    have hfilter_insert :
        (insert v0 ((P.voters.attach).image incl)).filter (fun v => TopRank P' v c) =
          insert v0 (((P.voters.attach).image incl).filter (fun v => TopRank P' v c)) := by
      simpa [Finset.filter_insert, htop_new_c]
    calc
      ((P'.voters.attach).filter (fun v => TopRank P' v c)).card
          = ((insert v0 ((P.voters.attach).image incl)).filter (fun v => TopRank P' v c)).card := by
            simpa [hattach]
      ((insert v0 ((P.voters.attach).image incl)).filter (fun v => TopRank P' v c)).card
          = (((P.voters.attach).image incl).filter (fun v => TopRank P' v c)).card + 1 := by
            simpa [hfilter_insert] using (Finset.card_insert_of_notMem hnot_mem_filter)
      _ = (((P.voters.attach).filter (fun w => TopRank P w c)).image incl).card + 1 := by
            simp [hfilter]
      _ = ((P.voters.attach).filter (fun w => TopRank P w c)).card + 1 := by
            simp [Finset.card_image_of_injective, hincl]
      _ = topCount P c + 1 := by rfl
  have topCount_addVoter_ne : ∀ d : Agenda P, d ≠ c → topCount P' d = topCount P d := by
    intro d hne
    have hattach : P'.voters.attach =
        insert v0 ((P.voters.attach).image incl) := by
      simp [P', v0, incl, addVoter, Finset.attach_insert]
    have hfilter :
        (((P.voters.attach).image incl).filter (fun w => TopRank P' w d)) =
          ((P.voters.attach).filter (fun w => TopRank P w d)).image incl := by
      simpa [htop_old] using
        (Finset.filter_image (s := P.voters.attach) (f := incl) (p := fun w => TopRank P' w d))
    have hnot_top : ¬ TopRank P' v0 d := htop_new_not d hne
    unfold topCount votersTop
    have hfilter_insert :
        (insert v0 ((P.voters.attach).image incl)).filter (fun v => TopRank P' v d) =
          (((P.voters.attach).image incl).filter (fun v => TopRank P' v d)) := by
      simpa [Finset.filter_insert, hnot_top]
    calc
      ((P'.voters.attach).filter (fun v => TopRank P' v d)).card
          = ((insert v0 ((P.voters.attach).image incl)).filter (fun v => TopRank P' v d)).card := by
            simpa [hattach]
      ((insert v0 ((P.voters.attach).image incl)).filter (fun v => TopRank P' v d)).card
          = (((P.voters.attach).image incl).filter (fun v => TopRank P' v d)).card := by
            simpa [hfilter_insert]
      _ = (((P.voters.attach).filter (fun w => TopRank P w d)).image incl).card := by
            simp [hfilter]
      _ = ((P.voters.attach).filter (fun w => TopRank P w d)).card := by
            simp [Finset.card_image_of_injective, hincl]
      _ = topCount P d := by rfl
  have hmax_old : ∀ d : Agenda P, topCount P d ≤ topCount P c := by
    have hc' : c ∈ P.candidates.attach.filter
        (fun c => ∀ d : Agenda P, topCount P d ≤ topCount P c) := by
      simpa [plurality] using hc
    exact (mem_filter.mp hc').2
  -- show c remains a plurality winner in the enlarged profile
  have hmax_new : ∀ d : Agenda P, topCount P' d ≤ topCount P' c := by
    intro d
    by_cases hne : d = c
    · simp [hne]
    · calc
        topCount P' d = topCount P d := topCount_addVoter_ne d hne
        _ ≤ topCount P c := hmax_old d
        _ ≤ topCount P c + 1 := Nat.le_succ _
        _ = topCount P' c := (topCount_addVoter_c).symm
  -- finish with membership in plurality
  have hcand : c ∈ P'.candidates.attach := by
    simpa [P', addVoter] using (Finset.mem_attach (s := P.candidates) c)
  have hc' : c ∈ P'.candidates.attach.filter
      (fun c => ∀ d : Agenda P', topCount P' d ≤ topCount P' c) := by
    exact mem_filter.mpr ⟨hcand, by simpa [P'] using hmax_new⟩
  simpa [P', plurality] using hc'

end FinsetApproach
