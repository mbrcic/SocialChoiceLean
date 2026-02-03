import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.ListBallot
import SocialChoice.Margin
import SocialChoice.Rules.PluralityWithRunoff.Defs
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.PluralityWithRunoff.Independence

namespace SocialChoice

open Finset

/-!
## PluralityWithRunoff fails independence of clones

Counterexample profile (candidates 0,1,2,3):
v0: 0 > 3 > 2 > 1
v1: 1 > 3 > 2 > 0
v2: 2 > 3 > 1 > 0
v3: 3 > 2 > 1 > 0

Clone set X = {2,3}. Candidate 1 is a winner in the full profile, but loses after removing
clone 3 (keeping representative 2).
-/

namespace PluralityWithRunoffClonesCounterexample

abbrev A4 := Fin 4
abbrev a : A4 := 0
abbrev b : A4 := 1
abbrev c : A4 := 2
abbrev d : A4 := 3

def ballot0321 : ListBallot 4 := ListBallot.mk' [0, 3, 2, 1]
def ballot1320 : ListBallot 4 := ListBallot.mk' [1, 3, 2, 0]
def ballot2310 : ListBallot 4 := ListBallot.mk' [2, 3, 1, 0]
def ballot3210 : ListBallot 4 := ListBallot.mk' [3, 2, 1, 0]

def ballots : Fin 4 → ListBallot 4
  | ⟨0, _⟩ => ballot0321
  | ⟨1, _⟩ => ballot1320
  | ⟨2, _⟩ => ballot2310
  | ⟨3, _⟩ => ballot3210

noncomputable def profile : Profile (Fin 4) A4 :=
  profileOfListBallots ballots

def cloneSet : Set A4 := {c, d}
abbrev rep : A4 := c

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · exact ⟨c, by simp [cloneSet]⟩
  intro v x hx
  fin_cases x
  · -- x = 0
    fin_cases v
    · -- v = 0: 0 above clones
      right
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot0321,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot0321,
            prefers_iff_prefersInList, prefersInList]; decide
    · -- v = 1: clones above 0
      left
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot1320,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot1320,
            prefers_iff_prefersInList, prefersInList]; decide
    · -- v = 2: clones above 0
      left
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot2310,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot2310,
            prefers_iff_prefersInList, prefersInList]; decide
    · -- v = 3: clones above 0
      left
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot3210,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot3210,
            prefers_iff_prefersInList, prefersInList]; decide
  · -- x = 1
    fin_cases v
    · -- v = 0: clones above 1
      left
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot0321,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot0321,
            prefers_iff_prefersInList, prefersInList]; decide
    · -- v = 1: 1 above clones
      right
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot1320,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot1320,
            prefers_iff_prefersInList, prefersInList]; decide
    · -- v = 2: clones above 1
      left
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot2310,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot2310,
            prefers_iff_prefersInList, prefersInList]; decide
    · -- v = 3: clones above 1
      left
      intro y hy
      have hy' : y = c ∨ y = d := by
        simpa [cloneSet] using hy
      cases hy' with
      | inl hyc =>
          subst hyc
          simp [profile, ballots, ballot3210,
            prefers_iff_prefersInList, prefersInList]; decide
      | inr hyd =>
          subst hyd
          simp [profile, ballots, ballot3210,
            prefers_iff_prefersInList, prefersInList]; decide
  · -- x = 2 (contradiction)
    have hmem : (2 : A4) ∈ cloneSet := by simp [cloneSet]
    exact (hx hmem).elim
  · -- x = 3 (contradiction)
    have hmem : (3 : A4) ∈ cloneSet := by simp [cloneSet]
    exact (hx hmem).elim

private lemma topCount_profile_0 : topCount profile (0 : A4) = 1 := by
  calc
    topCount profile (0 : A4) =
        countTop (fun v => (ballots v).ranking) 0 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (0 : A4)))
    _ = 1 := by decide

private lemma topCount_profile_1 : topCount profile (1 : A4) = 1 := by
  calc
    topCount profile (1 : A4) =
        countTop (fun v => (ballots v).ranking) 1 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (1 : A4)))
    _ = 1 := by decide

private lemma topCount_profile_2 : topCount profile (2 : A4) = 1 := by
  calc
    topCount profile (2 : A4) =
        countTop (fun v => (ballots v).ranking) 2 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (2 : A4)))
    _ = 1 := by decide

private lemma topCount_profile_3 : topCount profile (3 : A4) = 1 := by
  calc
    topCount profile (3 : A4) =
        countTop (fun v => (ballots v).ranking) 3 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (3 : A4)))
    _ = 1 := by decide

private lemma plurality_profile_has_0 : (0 : A4) ∈ plurality profile := by
  classical
  have hmax : ∀ d : A4, topCount profile d ≤ topCount profile (0 : A4) := by
    intro d
    fin_cases d <;> simp [topCount_profile_0, topCount_profile_1, topCount_profile_2, topCount_profile_3]
  have hmem :
      (0 : A4) ∈ (Finset.univ.filter
        (fun c => ∀ d : A4, topCount profile d ≤ topCount profile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_profile_has_1 : (1 : A4) ∈ plurality profile := by
  classical
  have hmax : ∀ d : A4, topCount profile d ≤ topCount profile (1 : A4) := by
    intro d
    fin_cases d <;> simp [topCount_profile_0, topCount_profile_1, topCount_profile_2, topCount_profile_3]
  have hmem :
      (1 : A4) ∈ (Finset.univ.filter
        (fun c => ∀ d : A4, topCount profile d ≤ topCount profile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma marginList_profile_1_0 :
    marginList (fun v => (ballots v).ranking) 1 0 = 2 := by
  decide

private lemma marginList_profile_1_2 :
    marginList (fun v => (ballots v).ranking) 1 2 = -2 := by
  decide

private lemma margin_profile_1_0 : margin profile (1 : A4) (0 : A4) = 2 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (1 : A4)) (b := (0 : A4))
  simpa [profile, marginList_profile_1_0] using h

private lemma margin_profile_1_2 : margin profile (1 : A4) (2 : A4) = -2 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (1 : A4)) (b := (2 : A4))
  simpa [profile, marginList_profile_1_2] using h

private lemma pair_10_mem_pairs :
    ({(1 : A4), (0 : A4)} : Finset A4) ∈ pluralityWithRunoffPairs profile := by
  classical
  have h0 : (0 : A4) ∈ plurality profile := plurality_profile_has_0
  have h1 : (1 : A4) ∈ plurality profile := plurality_profile_has_1
  have hS : (plurality profile).card ≥ 2 := by
    have hlt :
        1 < (plurality profile).card :=
      Finset.one_lt_card.mpr ⟨(0 : A4), h0, (1 : A4), h1, by decide⟩
    exact Nat.succ_le_iff.mp hlt
  have hsubset : ({(1 : A4), (0 : A4)} : Finset A4) ⊆ plurality profile := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    cases hx with
    | inl hx =>
        subst hx
        exact h1
    | inr hx =>
        subst hx
        exact h0
  have hcardpair : ({(1 : A4), (0 : A4)} : Finset A4).card = 2 := by
    simp
  have hmem :
      ({(1 : A4), (0 : A4)} : Finset A4) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma pluralityWithRunoff_profile_has_1 :
    (1 : A4) ∈ pluralityWithRunoff profile := by
  classical
  have hcard : ¬ Fintype.card A4 ≤ 1 := by decide
  have hmargin : 0 ≤ margin profile (1 : A4) (0 : A4) := by
    simp [margin_profile_1_0]
  have hpair : ({(1 : A4), (0 : A4)} : Finset A4) ∈ pluralityWithRunoffPairs profile :=
    pair_10_mem_pairs
  exact (mem_pluralityWithRunoff_iff (P := profile) (x := (1 : A4)) (hcard := hcard)).2
    ⟨(0 : A4), hpair, hmargin⟩

noncomputable def cloneProfile :
    Profile (Fin 4) {a : A4 // clonePred cloneSet rep a} :=
  removeClonesExcept profile cloneSet rep

private lemma clonePred_0 : clonePred cloneSet rep (0 : A4) := by
  left
  intro hmem
  have hmem' : (0 : A4) = c ∨ (0 : A4) = d := by
    simpa [cloneSet] using hmem
  cases hmem' with
  | inl h =>
      exact (by decide : (0 : A4) ≠ c) h
  | inr h =>
      exact (by decide : (0 : A4) ≠ d) h

private lemma clonePred_1 : clonePred cloneSet rep (1 : A4) := by
  left
  intro hmem
  have hmem' : (1 : A4) = c ∨ (1 : A4) = d := by
    simpa [cloneSet] using hmem
  cases hmem' with
  | inl h =>
      exact (by decide : (1 : A4) ≠ c) h
  | inr h =>
      exact (by decide : (1 : A4) ≠ d) h

private lemma clonePred_2 : clonePred cloneSet rep (2 : A4) := by
  right
  rfl

abbrev cand0 : {a : A4 // clonePred cloneSet rep a} :=
  ⟨0, clonePred_0⟩

abbrev cand1 : {a : A4 // clonePred cloneSet rep a} :=
  ⟨1, clonePred_1⟩

abbrev cand2 : {a : A4 // clonePred cloneSet rep a} :=
  ⟨2, clonePred_2⟩

private lemma cand0_ne_cand1 : cand0 ≠ cand1 := by
  intro h
  have h' : (0 : A4) = (1 : A4) := by
    simpa using congrArg Subtype.val h
  exact (by decide : (0 : A4) ≠ (1 : A4)) h'

private lemma cand0_ne_cand2 : cand0 ≠ cand2 := by
  intro h
  have h' : (0 : A4) = (2 : A4) := by
    simpa using congrArg Subtype.val h
  exact (by decide : (0 : A4) ≠ (2 : A4)) h'

private lemma cand1_ne_cand2 : cand1 ≠ cand2 := by
  intro h
  have h' : (1 : A4) = (2 : A4) := by
    simpa using congrArg Subtype.val h
  exact (by decide : (1 : A4) ≠ (2 : A4)) h'

private lemma clonePred_cases (x : {a : A4 // clonePred cloneSet rep a}) :
    x = cand0 ∨ x = cand1 ∨ x = cand2 := by
  rcases x with ⟨x, hx⟩
  fin_cases x
  · left
    apply Subtype.ext
    rfl
  · right
    left
    apply Subtype.ext
    rfl
  · right
    right
    apply Subtype.ext
    rfl
  · have : False := by
      have hx' : (3 : A4) ∉ cloneSet ∨ (3 : A4) = rep := by
        simpa [clonePred] using hx
      cases hx' with
      | inl hnot =>
          have : False := by
            simp [cloneSet] at hnot
          exact this
      | inr hEq =>
          exact (by decide : (3 : A4) ≠ rep) hEq
    exact this.elim

private lemma prefers_cloneProfile_of_profile (v : Fin 4) (a b : A4)
    (ha : clonePred cloneSet rep a) (hb : clonePred cloneSet rep b)
    (h : Prefers profile v a b) :
    Prefers cloneProfile v ⟨a, ha⟩ ⟨b, hb⟩ := by
  simpa [cloneProfile, removeClonesExcept, prefers_restrictCandidates_iff] using h

private lemma not_topRank_of_prefers (v : Fin 4)
    {c d : {a : A4 // clonePred cloneSet rep a}} (hcd : d ≠ c)
    (h : Prefers cloneProfile v d c) : ¬ TopRank cloneProfile v c := by
  intro htop
  have htop' : Prefers cloneProfile v c d := htop d (by simpa [eq_comm] using hcd)
  let _ : Preorder {a : A4 // clonePred cloneSet rep a} := (cloneProfile.pref v).toPreorder
  have htop'' : (cloneProfile.pref v).lt c d := by
    simpa [Prefers] using htop'
  have h'' : (cloneProfile.pref v).lt d c := by
    simpa [Prefers] using h
  exact (lt_asymm (a := c) (b := d) htop'') h''

private lemma topRank_cloneProfile_v0_cand0 :
    TopRank cloneProfile (0 : Fin 4) cand0 := by
  intro d hd
  rcases clonePred_cases d with hd0 | hd1
  · subst hd0
    exact (hd rfl).elim
  · rcases hd1 with hd1 | hd2
    · subst hd1
      have h :
          Prefers profile (0 : Fin 4) (0 : A4) (1 : A4) := by
        simp [profile, ballots, ballot0321, prefers_iff_prefersInList, prefersInList]; decide
      exact prefers_cloneProfile_of_profile (v := 0) (a := 0) (b := 1)
        clonePred_0 clonePred_1 h
    · subst hd2
      have h :
          Prefers profile (0 : Fin 4) (0 : A4) (2 : A4) := by
        simp [profile, ballots, ballot0321, prefers_iff_prefersInList, prefersInList]; decide
      exact prefers_cloneProfile_of_profile (v := 0) (a := 0) (b := 2)
        clonePred_0 clonePred_2 h

private lemma topRank_cloneProfile_v1_cand1 :
    TopRank cloneProfile (1 : Fin 4) cand1 := by
  intro d hd
  rcases clonePred_cases d with hd0 | hd1
  · subst hd0
    have h :
        Prefers profile (1 : Fin 4) (1 : A4) (0 : A4) := by
      simp [profile, ballots, ballot1320, prefers_iff_prefersInList, prefersInList]; decide
    exact prefers_cloneProfile_of_profile (v := 1) (a := 1) (b := 0)
      clonePred_1 clonePred_0 h
  · rcases hd1 with hd1 | hd2
    · subst hd1
      exact (hd rfl).elim
    · subst hd2
      have h :
          Prefers profile (1 : Fin 4) (1 : A4) (2 : A4) := by
        simp [profile, ballots, ballot1320, prefers_iff_prefersInList, prefersInList]; decide
      exact prefers_cloneProfile_of_profile (v := 1) (a := 1) (b := 2)
        clonePred_1 clonePred_2 h

private lemma topRank_cloneProfile_v2_cand2 :
    TopRank cloneProfile (2 : Fin 4) cand2 := by
  intro d hd
  rcases clonePred_cases d with hd0 | hd1
  · subst hd0
    have h :
        Prefers profile (2 : Fin 4) (2 : A4) (0 : A4) := by
      simp [profile, ballots, ballot2310, prefers_iff_prefersInList, prefersInList]; decide
    exact prefers_cloneProfile_of_profile (v := 2) (a := 2) (b := 0)
      clonePred_2 clonePred_0 h
  · rcases hd1 with hd1 | hd2
    · subst hd1
      have h :
          Prefers profile (2 : Fin 4) (2 : A4) (1 : A4) := by
        simp [profile, ballots, ballot2310, prefers_iff_prefersInList, prefersInList]; decide
      exact prefers_cloneProfile_of_profile (v := 2) (a := 2) (b := 1)
        clonePred_2 clonePred_1 h
    · subst hd2
      exact (hd rfl).elim

private lemma topRank_cloneProfile_v3_cand2 :
    TopRank cloneProfile (3 : Fin 4) cand2 := by
  intro d hd
  rcases clonePred_cases d with hd0 | hd1
  · subst hd0
    have h :
        Prefers profile (3 : Fin 4) (2 : A4) (0 : A4) := by
      simp [profile, ballots, ballot3210, prefers_iff_prefersInList, prefersInList]; decide
    exact prefers_cloneProfile_of_profile (v := 3) (a := 2) (b := 0)
      clonePred_2 clonePred_0 h
  · rcases hd1 with hd1 | hd2
    · subst hd1
      have h :
          Prefers profile (3 : Fin 4) (2 : A4) (1 : A4) := by
        simp [profile, ballots, ballot3210, prefers_iff_prefersInList, prefersInList]; decide
      exact prefers_cloneProfile_of_profile (v := 3) (a := 2) (b := 1)
        clonePred_2 clonePred_1 h
    · subst hd2
      exact (hd rfl).elim

private lemma not_topRank_cloneProfile_v1_cand0 :
    ¬ TopRank cloneProfile (1 : Fin 4) cand0 := by
  have h :
      Prefers profile (1 : Fin 4) (1 : A4) (0 : A4) := by
    simp [profile, ballots, ballot1320, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (1 : Fin 4) cand1 cand0 :=
    prefers_cloneProfile_of_profile (v := 1) (a := 1) (b := 0)
      clonePred_1 clonePred_0 h
  exact not_topRank_of_prefers (v := 1) cand0_ne_cand1.symm h'

private lemma not_topRank_cloneProfile_v2_cand0 :
    ¬ TopRank cloneProfile (2 : Fin 4) cand0 := by
  have h :
      Prefers profile (2 : Fin 4) (2 : A4) (0 : A4) := by
    simp [profile, ballots, ballot2310, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (2 : Fin 4) cand2 cand0 :=
    prefers_cloneProfile_of_profile (v := 2) (a := 2) (b := 0)
      clonePred_2 clonePred_0 h
  exact not_topRank_of_prefers (v := 2) cand0_ne_cand2.symm h'

private lemma not_topRank_cloneProfile_v3_cand0 :
    ¬ TopRank cloneProfile (3 : Fin 4) cand0 := by
  have h :
      Prefers profile (3 : Fin 4) (2 : A4) (0 : A4) := by
    simp [profile, ballots, ballot3210, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (3 : Fin 4) cand2 cand0 :=
    prefers_cloneProfile_of_profile (v := 3) (a := 2) (b := 0)
      clonePred_2 clonePred_0 h
  exact not_topRank_of_prefers (v := 3) cand0_ne_cand2.symm h'

private lemma not_topRank_cloneProfile_v0_cand1 :
    ¬ TopRank cloneProfile (0 : Fin 4) cand1 := by
  have h :
      Prefers profile (0 : Fin 4) (0 : A4) (1 : A4) := by
    simp [profile, ballots, ballot0321, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (0 : Fin 4) cand0 cand1 :=
    prefers_cloneProfile_of_profile (v := 0) (a := 0) (b := 1)
      clonePred_0 clonePred_1 h
  exact not_topRank_of_prefers (v := 0) cand0_ne_cand1 h'

private lemma not_topRank_cloneProfile_v2_cand1 :
    ¬ TopRank cloneProfile (2 : Fin 4) cand1 := by
  have h :
      Prefers profile (2 : Fin 4) (2 : A4) (1 : A4) := by
    simp [profile, ballots, ballot2310, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (2 : Fin 4) cand2 cand1 :=
    prefers_cloneProfile_of_profile (v := 2) (a := 2) (b := 1)
      clonePred_2 clonePred_1 h
  exact not_topRank_of_prefers (v := 2) cand1_ne_cand2.symm h'

private lemma not_topRank_cloneProfile_v3_cand1 :
    ¬ TopRank cloneProfile (3 : Fin 4) cand1 := by
  have h :
      Prefers profile (3 : Fin 4) (2 : A4) (1 : A4) := by
    simp [profile, ballots, ballot3210, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (3 : Fin 4) cand2 cand1 :=
    prefers_cloneProfile_of_profile (v := 3) (a := 2) (b := 1)
      clonePred_2 clonePred_1 h
  exact not_topRank_of_prefers (v := 3) cand1_ne_cand2.symm h'

private lemma not_topRank_cloneProfile_v0_cand2 :
    ¬ TopRank cloneProfile (0 : Fin 4) cand2 := by
  have h :
      Prefers profile (0 : Fin 4) (0 : A4) (2 : A4) := by
    simp [profile, ballots, ballot0321, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (0 : Fin 4) cand0 cand2 :=
    prefers_cloneProfile_of_profile (v := 0) (a := 0) (b := 2)
      clonePred_0 clonePred_2 h
  exact not_topRank_of_prefers (v := 0) cand0_ne_cand2 h'

private lemma not_topRank_cloneProfile_v1_cand2 :
    ¬ TopRank cloneProfile (1 : Fin 4) cand2 := by
  have h :
      Prefers profile (1 : Fin 4) (1 : A4) (2 : A4) := by
    simp [profile, ballots, ballot1320, prefers_iff_prefersInList, prefersInList]; decide
  have h' :
      Prefers cloneProfile (1 : Fin 4) cand1 cand2 :=
    prefers_cloneProfile_of_profile (v := 1) (a := 1) (b := 2)
      clonePred_1 clonePred_2 h
  exact not_topRank_of_prefers (v := 1) cand1_ne_cand2 h'

private lemma votersTop_cloneProfile_0 :
    votersTop cloneProfile cand0 = ({0} : Finset (Fin 4)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersTop, topRank_cloneProfile_v0_cand0, not_topRank_cloneProfile_v1_cand0,
      not_topRank_cloneProfile_v2_cand0, not_topRank_cloneProfile_v3_cand0]

private lemma votersTop_cloneProfile_1 :
    votersTop cloneProfile cand1 = ({1} : Finset (Fin 4)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersTop, topRank_cloneProfile_v1_cand1, not_topRank_cloneProfile_v0_cand1,
      not_topRank_cloneProfile_v2_cand1, not_topRank_cloneProfile_v3_cand1]

private lemma votersTop_cloneProfile_2 :
    votersTop cloneProfile cand2 = ({2, 3} : Finset (Fin 4)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersTop, topRank_cloneProfile_v2_cand2, topRank_cloneProfile_v3_cand2,
      not_topRank_cloneProfile_v0_cand2, not_topRank_cloneProfile_v1_cand2]

private lemma topCount_cloneProfile_0 : topCount cloneProfile cand0 = 1 := by
  classical
  simp [topCount, votersTop_cloneProfile_0]

private lemma topCount_cloneProfile_1 : topCount cloneProfile cand1 = 1 := by
  classical
  simp [topCount, votersTop_cloneProfile_1]

private lemma topCount_cloneProfile_2 : topCount cloneProfile cand2 = 2 := by
  classical
  simp [topCount, votersTop_cloneProfile_2]

private lemma plurality_cloneProfile_has_2 : cand2 ∈ plurality cloneProfile := by
  classical
  have hmax : ∀ d : {a : A4 // clonePred cloneSet rep a},
      topCount cloneProfile d ≤ topCount cloneProfile cand2 := by
    intro d
    rcases clonePred_cases d with hd0 | hd1
    · subst hd0
      simp [topCount_cloneProfile_0, topCount_cloneProfile_2]
    · rcases hd1 with hd1 | hd2
      · subst hd1
        simp [topCount_cloneProfile_1, topCount_cloneProfile_2]
      · subst hd2
        simp [topCount_cloneProfile_2]
  have hmem :
      cand2 ∈ (Finset.univ.filter
        (fun c => ∀ d, topCount cloneProfile d ≤ topCount cloneProfile c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_cloneProfile_not_0 : cand0 ∉ plurality cloneProfile := by
  intro hmem
  have hmax := (Finset.mem_filter.mp hmem).2
  have h := hmax cand2
  have h' : (2 : Nat) ≤ 1 := by
    simp [topCount_cloneProfile_0, topCount_cloneProfile_2] at h
  exact (by decide : ¬ ((2 : Nat) ≤ 1)) h'

private lemma plurality_cloneProfile_not_1 : cand1 ∉ plurality cloneProfile := by
  intro hmem
  have hmax := (Finset.mem_filter.mp hmem).2
  have h := hmax cand2
  have h' : (2 : Nat) ≤ 1 := by
    simp [topCount_cloneProfile_1, topCount_cloneProfile_2] at h
  exact (by decide : ¬ ((2 : Nat) ≤ 1)) h'

private lemma plurality_cloneProfile_eq :
    plurality cloneProfile = ({cand2} : Finset {a : A4 // clonePred cloneSet rep a}) := by
  classical
  apply Finset.ext
  intro x
  rcases clonePred_cases x with hx0 | hx1
  · subst hx0
    simp [plurality_cloneProfile_not_0]
  · rcases hx1 with hx1 | hx2
    · subst hx1
      simp [plurality_cloneProfile_not_1]
    · subst hx2
      simp [plurality_cloneProfile_has_2]

private lemma margin_cloneProfile_1_2 :
    margin cloneProfile cand1 cand2 = -2 := by
  have h :=
    margin_eq_margin_restrictCandidates (P := profile) (p := clonePred cloneSet rep)
      (a := cand1) (b := cand2)
  -- rewrite to original margin
  simpa [cand1, cand2, margin_profile_1_2, cloneProfile, removeClonesExcept] using h.symm

private lemma pluralityWithRunoff_cloneProfile_not_1 :
    cand1 ∉ pluralityWithRunoff cloneProfile := by
  classical
  have hcard : ¬ Fintype.card {a : A4 // clonePred cloneSet rep a} ≤ 1 := by
    intro hle
    have hsub : Subsingleton {a : A4 // clonePred cloneSet rep a} :=
      (Fintype.card_le_one_iff_subsingleton.mp hle)
    have hne : cand0 ≠ cand1 := cand0_ne_cand1
    exact hne (Subsingleton.elim cand0 cand1)
  intro hmem
  rcases (mem_pluralityWithRunoff_iff (P := cloneProfile) (x := cand1) (hcard := hcard)).1 hmem with
    ⟨y, hyPair, hmargin⟩
  have hS : plurality cloneProfile = ({cand2} : Finset {a : A4 // clonePred cloneSet rep a}) :=
    plurality_cloneProfile_eq
  have hS_card : ¬ (plurality cloneProfile).card ≥ 2 := by
    simp [hS]
  have hyPair' :
      ({cand1, y} : Finset {a : A4 // clonePred cloneSet rep a}) ∈
        ((plurality cloneProfile).product
          (secondPluralitySet cloneProfile (plurality cloneProfile))).image
            (fun p => ({p.1, p.2} : Finset {a : A4 // clonePred cloneSet rep a})) := by
    simpa [pluralityWithRunoffPairs, hS_card] using hyPair
  rcases Finset.mem_image.mp hyPair' with ⟨p, hp, hpair_eq⟩
  rcases Finset.mem_product.mp hp with ⟨hp1, _hp2⟩
  have hp1' : p.1 = cand2 := by
    have : p.1 ∈ ({cand2} : Finset {a : A4 // clonePred cloneSet rep a}) := by
      simpa [hS] using hp1
    simpa using (Finset.mem_singleton.mp this)
  have hmem_cand2 :
      cand2 ∈ ({cand1, y} : Finset {a : A4 // clonePred cloneSet rep a}) := by
    have : cand2 ∈ ({p.1, p.2} :
        Finset {a : A4 // clonePred cloneSet rep a}) := by
      simp [hp1']
    simpa [hpair_eq] using this
  have hy : y = cand2 := by
    have hy' : cand2 = cand1 ∨ cand2 = y := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem_cand2
    cases hy' with
    | inl h =>
        exact (by cases cand1_ne_cand2.symm h)
    | inr h =>
        exact h.symm
  subst hy
  have hneg : ¬ (0 ≤ margin cloneProfile cand1 cand2) := by
    simp [margin_cloneProfile_1_2]
  exact (hneg hmargin).elim

end PluralityWithRunoffClonesCounterexample

open PluralityWithRunoffClonesCounterexample

theorem pluralityWithRunoff_not_independenceOfClones :
    ¬ IndependenceOfClones pluralityWithRunoff := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : rep ∈ cloneSet := by
    simp [cloneSet, rep]
  have h := hind (P := profile) (X := cloneSet) (x := rep) hclone hx
  have hc : (1 : A4) ∉ cloneSet := by
    intro hmem
    have hmem' :
        (1 : A4) = c ∨ (1 : A4) = d := by
      simpa [cloneSet] using hmem
    cases hmem' with
    | inl h =>
        exact (by decide : (1 : A4) ≠ c) h
    | inr h =>
        exact (by decide : (1 : A4) ≠ d) h
  have hnonclone := h.1 (1 : A4) hc
  have hleft :
      (⟨(1 : A4), Or.inl hc⟩ :
        {a : A4 // clonePred cloneSet rep a}) ∈
        pluralityWithRunoff (removeClonesExcept profile cloneSet rep) := by
    simpa using (hnonclone).1 pluralityWithRunoff_profile_has_1
  exact (pluralityWithRunoff_cloneProfile_not_1 hleft).elim

end SocialChoice
