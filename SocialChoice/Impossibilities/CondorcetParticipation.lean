import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Participation
import SocialChoice.Examples
import Mathlib.Tactic.FinCases

namespace SocialChoice

open Finset

def ballotABDC : ListBallot 4 := ListBallot.mk' [0, 1, 3, 2]
def ballotBDCA : ListBallot 4 := ListBallot.mk' [1, 3, 2, 0]
def ballotCABD : ListBallot 4 := ListBallot.mk' [2, 0, 1, 3]
def ballotDCAB : ListBallot 4 := ListBallot.mk' [3, 2, 0, 1]
def ballotABCD : ListBallot 4 := ListBallot.mk' [0, 1, 2, 3]

def P0Ballots : Fin 10 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB

noncomputable def P0Profile : Profile (Fin 10) (Fin 4) :=
  profileOfListBallots P0Ballots

def P1Ballots : Fin 12 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotABCD
  | 11 => ballotABCD

noncomputable def P1Profile : Profile (Fin 12) (Fin 4) :=
  profileOfListBallots P1Ballots

def P3Ballots : Fin 10 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotABCD
  | 9 => ballotABCD

noncomputable def P3Profile : Profile (Fin 10) (Fin 4) :=
  profileOfListBallots P3Ballots

def V0 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
def V10 : Finset (Fin 12) := insert (10 : Fin 12) V0
def V11 : Finset (Fin 12) := insert (11 : Fin 12) V10
def V2set : Finset (Fin 12) := {0, 1, 5, 6, 7, 8, 9, 10, 11}
def V3set : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 10, 11}
def V4 : Finset (Fin 12) := {0, 1, 2, 3, 4, 10, 11}

noncomputable def profileOnSubset (S : Finset (Fin 12)) :
    Profile (Electorate (Fin 12) S) (Fin 4) :=
  { pref := fun v => (P1Ballots v.1).toLinearOrder }

noncomputable def P0ProfileSub : Profile (Electorate (Fin 12) V0) (Fin 4) :=
  profileOnSubset V0

noncomputable def P10ProfileSub : Profile (Electorate (Fin 12) V10) (Fin 4) :=
  profileOnSubset V10

noncomputable def P1ProfileSub : Profile (Electorate (Fin 12) V11) (Fin 4) :=
  profileOnSubset V11

noncomputable def P2ProfileSub : Profile (Electorate (Fin 12) V2set) (Fin 4) :=
  profileOnSubset V2set

noncomputable def P3ProfileSub : Profile (Electorate (Fin 12) V3set) (Fin 4) :=
  profileOnSubset V3set

noncomputable def P4ProfileSub : Profile (Electorate (Fin 12) V4) (Fin 4) :=
  profileOnSubset V4

lemma ten_not_mem_V0 : (10 : Fin 12) ∉ V0 := by decide
lemma eleven_not_mem_V10 : (11 : Fin 12) ∉ V10 := by decide

lemma P10_agrees_V0 :
    ∀ v : Electorate (Fin 12) V0,
      P10ProfileSub.pref (liftVoter (u := (10 : Fin 12)) v) = P0ProfileSub.pref v := by
  intro v
  rfl

lemma P1_agrees_V10 :
    ∀ v : Electorate (Fin 12) V10,
      P1ProfileSub.pref (liftVoter (u := (11 : Fin 12)) v) = P10ProfileSub.pref v := by
  intro v
  rfl

lemma P10_newVoter_pref :
    P10ProfileSub.pref (newVoter (u := (10 : Fin 12)) (V := V0) ten_not_mem_V0) =
      ballotABCD.toLinearOrder := by
  rfl

lemma P1_newVoter_pref :
    P1ProfileSub.pref (newVoter (u := (11 : Fin 12)) (V := V10) eleven_not_mem_V10) =
      ballotABCD.toLinearOrder := by
  rfl

lemma ballotABCD_lt_of_mem_ab_not_mem (x y : Fin 4)
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hy : y ∉ ({0, 1} : Finset (Fin 4))) :
    ballotABCD.toLinearOrder.lt x y := by
  fin_cases x
  · fin_cases y
    · simp [Finset.mem_insert, Finset.mem_singleton] at hy
    · simp [Finset.mem_insert, Finset.mem_singleton] at hy
    · simp [ballotABCD, ListBallot.lt_iff_idxOf]; decide
    · simp [ballotABCD, ListBallot.lt_iff_idxOf]; decide
  · fin_cases y
    · simp [Finset.mem_insert, Finset.mem_singleton] at hy
    · simp [Finset.mem_insert, Finset.mem_singleton] at hy
    · simp [ballotABCD, ListBallot.lt_iff_idxOf]; decide
    · simp [ballotABCD, ListBallot.lt_iff_idxOf]; decide
  · simp [Finset.mem_insert, Finset.mem_singleton] at hx
  · simp [Finset.mem_insert, Finset.mem_singleton] at hx

lemma ballotABCD_not_lt_iff_mem_ab {x y : Fin 4}
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hnot : ¬ ballotABCD.toLinearOrder.lt x y) :
    y ∈ ({0, 1} : Finset (Fin 4)) := by
  by_contra hy
  exact hnot (ballotABCD_lt_of_mem_ab_not_mem x y hx hy)

lemma participation_add_10 {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : f P0ProfileSub = {x}) (hy : f P10ProfileSub = {y}) :
    ¬ (P10ProfileSub.pref (newVoter (u := (10 : Fin 12)) (V := V0) ten_not_mem_V0)).lt x y := by
  apply hpart (V := V0) (u := (10 : Fin 12)) ten_not_mem_V0 P0ProfileSub P10ProfileSub x y
  · exact P10_agrees_V0
  · exact hx
  · exact hy

lemma participation_add_11 {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : f P10ProfileSub = {x}) (hy : f P1ProfileSub = {y}) :
    ¬ (P1ProfileSub.pref (newVoter (u := (11 : Fin 12)) (V := V10) eleven_not_mem_V10)).lt x y := by
  apply hpart (V := V10) (u := (11 : Fin 12)) eleven_not_mem_V10 P10ProfileSub P1ProfileSub x y
  · exact P1_agrees_V10
  · exact hx
  · exact hy

lemma P0_to_P10_preserve_ab {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hP0 : f P0ProfileSub = {x}) (hP10 : f P10ProfileSub = {y}) :
    y ∈ ({0, 1} : Finset (Fin 4)) := by
  have hnot :
      ¬ ballotABCD.toLinearOrder.lt x y := by
    simpa [P10_newVoter_pref] using participation_add_10 hf hpart hP0 hP10
  exact ballotABCD_not_lt_iff_mem_ab hx hnot

lemma P10_to_P1_preserve_ab {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hP10 : f P10ProfileSub = {x}) (hP1 : f P1ProfileSub = {y}) :
    y ∈ ({0, 1} : Finset (Fin 4)) := by
  have hnot :
      ¬ ballotABCD.toLinearOrder.lt x y := by
    simpa [P1_newVoter_pref] using participation_add_11 hf hpart hP10 hP1
  exact ballotABCD_not_lt_iff_mem_ab hx hnot

lemma P0_to_P1_preserve_ab {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hP0 : f P0ProfileSub = {x}) (hP1 : f P1ProfileSub = {y}) :
    y ∈ ({0, 1} : Finset (Fin 4)) := by
  have hcard : (f P10ProfileSub).card = 1 := by
    simpa using (hf P10ProfileSub)
  rcases Finset.card_eq_one.mp hcard with ⟨z, hz⟩
  have hz_mem : z ∈ ({0, 1} : Finset (Fin 4)) :=
    P0_to_P10_preserve_ab hf hpart hx hP0 hz
  exact P10_to_P1_preserve_ab hf hpart hz_mem hz hP1

def P2Ballots : Fin 9 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotCABD
  | 3 => ballotCABD
  | 4 => ballotCABD
  | 5 => ballotDCAB
  | 6 => ballotDCAB
  | 7 => ballotABCD
  | 8 => ballotABCD

noncomputable def P2Profile : Profile (Fin 9) (Fin 4) :=
  profileOfListBallots P2Ballots

def P4Ballots : Fin 7 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotABCD
  | 6 => ballotABCD

noncomputable def P4Profile : Profile (Fin 7) (Fin 4) :=
  profileOfListBallots P4Ballots

lemma votersPreferring_card_eq_countPrefers {m n : ℕ}
    (ballots : Fin m → ListBallot n) (a b : Fin n) :
    (votersPreferring (profileOfListBallots ballots) a b).card =
      countPrefers (fun v => (ballots v).ranking) a b := by
  unfold countPrefers
  rw [votersPreferring_eq_filter_prefersInList]

lemma strictMajority_fin9 {S : Finset (Fin 9)} (hcard : S.card = 5) :
    StrictMajority S := by
  unfold StrictMajority
  have h : (2 * (5 : Nat) > (9 : Nat)) := by decide
  simpa [hcard] using h

lemma strictMajority_fin7 {S : Finset (Fin 7)} (hcard : S.card = 4) :
    StrictMajority S := by
  unfold StrictMajority
  have h : (2 * (4 : Nat) > (7 : Nat)) := by decide
  simpa [hcard] using h

lemma P2_prefers_card_c_a : (votersPreferring P2Profile (2 : Fin 4) 0).card = 5 := by
  have hcount : countPrefers (fun v => (P2Ballots v).ranking) 2 0 = 5 := rfl
  simpa [P2Profile, votersPreferring_card_eq_countPrefers] using hcount

lemma P2_prefers_card_c_b : (votersPreferring P2Profile (2 : Fin 4) 1).card = 5 := by
  have hcount : countPrefers (fun v => (P2Ballots v).ranking) 2 1 = 5 := rfl
  simpa [P2Profile, votersPreferring_card_eq_countPrefers] using hcount

lemma P2_prefers_card_c_d : (votersPreferring P2Profile (2 : Fin 4) 3).card = 5 := by
  have hcount : countPrefers (fun v => (P2Ballots v).ranking) 2 3 = 5 := rfl
  simpa [P2Profile, votersPreferring_card_eq_countPrefers] using hcount

lemma P4_prefers_card_a_b : (votersPreferring P4Profile (0 : Fin 4) 1).card = 4 := by
  have hcount : countPrefers (fun v => (P4Ballots v).ranking) 0 1 = 4 := rfl
  simpa [P4Profile, votersPreferring_card_eq_countPrefers] using hcount

lemma P4_prefers_card_a_c : (votersPreferring P4Profile (0 : Fin 4) 2).card = 4 := by
  have hcount : countPrefers (fun v => (P4Ballots v).ranking) 0 2 = 4 := rfl
  simpa [P4Profile, votersPreferring_card_eq_countPrefers] using hcount

lemma P4_prefers_card_a_d : (votersPreferring P4Profile (0 : Fin 4) 3).card = 4 := by
  have hcount : countPrefers (fun v => (P4Ballots v).ranking) 0 3 = 4 := rfl
  simpa [P4Profile, votersPreferring_card_eq_countPrefers] using hcount

lemma P2_condorcet_winner_c : CondorcetWinner P2Profile (2 : Fin 4) := by
  intro d hd
  fin_cases d
  · exact strictMajority_fin9 P2_prefers_card_c_a
  · exact strictMajority_fin9 P2_prefers_card_c_b
  · cases hd rfl
  · exact strictMajority_fin9 P2_prefers_card_c_d

lemma P4_condorcet_winner_a : CondorcetWinner P4Profile (0 : Fin 4) := by
  intro d hd
  fin_cases d
  · cases hd rfl
  · exact strictMajority_fin7 P4_prefers_card_a_b
  · exact strictMajority_fin7 P4_prefers_card_a_c
  · exact strictMajority_fin7 P4_prefers_card_a_d

end SocialChoice
