import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Participation
import SocialChoice.Examples
import Mathlib.Tactic

/-
This file contains a proof that no voting rule can satisfy
resoluteness, Condorcet consistency, and resolute participation
simultaneously. It works by analyzing several explicit profiles
with m=4 alternatvies and up to n=12 voters.

The proof follows the computer-aided proof of Theorem 3 in
Brandt et al. (2016).
-/

namespace SocialChoice

open Finset

-- Ballots used in the proof
def ballotABCD : ListBallot 4 := ListBallot.mk' [0, 1, 2, 3]
def ballotABDC : ListBallot 4 := ListBallot.mk' [0, 1, 3, 2]
def ballotBDCA : ListBallot 4 := ListBallot.mk' [1, 3, 2, 0]
def ballotCABD : ListBallot 4 := ListBallot.mk' [2, 0, 1, 3]
def ballotDCAB : ListBallot 4 := ListBallot.mk' [3, 2, 0, 1]
def ballotDCBA : ListBallot 4 := ListBallot.mk' [3, 2, 1, 0]

-- The master list of ballots for the maximum profiles (P1) and (P5)
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

-- The master list of ballots for the maximum profile (P1)
def P5Ballots : Fin 12 → ListBallot 4
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
  | 10 => ballotDCBA
  | 11 => ballotDCBA

-- Sets of voters for different profiles
def V0 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
def V1 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
def V2 : Finset (Fin 12) := {0, 1, 5, 6, 7, 8, 9, 10, 11}
def V3 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 10, 11}
def V4 : Finset (Fin 12) := {0, 1, 2, 3, 4, 10, 11}
def V5 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
def V6 : Finset (Fin 12) := {0, 1, 2, 3, 4, 8, 9, 10, 11}
def V7 : Finset (Fin 12) := {2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
def V8 : Finset (Fin 12) := {5, 6, 7, 8, 9, 10, 11}

-- Generic profile definition on a subset of voters, using P1Ballots
noncomputable def profileOnSubset (S : Finset (Fin 12)) :
    Profile (Electorate (Fin 12) S) (Fin 4) :=
  { pref := fun v => (P1Ballots v.1).toLinearOrder }

-- Specific profiles
noncomputable def P0ProfileSub : Profile (Electorate (Fin 12) V0) (Fin 4) :=
  profileOnSubset V0

noncomputable def P1ProfileSub : Profile (Electorate (Fin 12) V1) (Fin 4) :=
  profileOnSubset V1

noncomputable def P2ProfileSub : Profile (Electorate (Fin 12) V2) (Fin 4) :=
  profileOnSubset V2

noncomputable def P3ProfileSub : Profile (Electorate (Fin 12) V3) (Fin 4) :=
  profileOnSubset V3

noncomputable def P4ProfileSub : Profile (Electorate (Fin 12) V4) (Fin 4) :=
  profileOnSubset V4

-- TODO: the following profiles use P5Ballots instead of P1Ballots
-- will probably need to prove that P0ProfileSub wrt P5Ballots is the same as
-- P0ProfileSub wrt P1Ballots (since P0 is the common starting profile)

noncomputable def P5ProfileSub : Profile (Electorate (Fin 12) V5) (Fin 4) :=
  profileOnSubset V5

noncomputable def P6ProfileSub : Profile (Electorate (Fin 12) V6) (Fin 4) :=
  profileOnSubset V6

noncomputable def P7ProfileSub : Profile (Electorate (Fin 12) V7) (Fin 4) :=
  profileOnSubset V7

noncomputable def P8ProfileSub : Profile (Electorate (Fin 12) V8) (Fin 4) :=
  profileOnSubset V8

-- Lemma for restrictProfile equality
lemma restrictProfile_eq_profileOnSubset {S T : Finset (Fin 12)} (hST : S ⊆ T) :
    restrictProfile (profileOnSubset T) S hST = profileOnSubset S := by
  simp [restrictProfile, profileOnSubset]

-- UpperSet properties for the ballots

lemma ballotABCD_UpperSet_ab : UpperSet ballotABCD.toLinearOrder ({0, 1} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotABCD, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotBDCA_UpperSet_not_a : UpperSet ballotBDCA.toLinearOrder ({1, 2, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotBDCA, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotDCAB_UpperSet_not_b : UpperSet ballotDCAB.toLinearOrder ({0, 2, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotDCAB, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotCABD_UpperSet_ca : UpperSet ballotCABD.toLinearOrder ({0, 2} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotCABD, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotDCBA_UpperSet_dc : UpperSet ballotDCBA.toLinearOrder ({2, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotDCBA, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotCABD_UpperSet_not_d : UpperSet ballotCABD.toLinearOrder ({0, 1, 2} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotCABD, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotABDC_UpperSet_not_c : UpperSet ballotABDC.toLinearOrder ({0, 1, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotABDC, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotBDCA_UpperSet_bd : UpperSet ballotBDCA.toLinearOrder ({1, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotBDCA, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

-- Proof steps using resoluteParticipation_superset

lemma P0_to_P1_preserve_ab {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hP0 : f P0ProfileSub = {x}) (hP1 : f P1ProfileSub = {y}) :
    y ∈ ({0, 1} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {0, 1}
  have hsubset : f P1ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V0 V1 (by simp [V0, V1]) P1ProfileSub S x
    · erw [restrictProfile_eq_profileOnSubset (hST := by simp [V0, V1])]
      exact hP0
    · exact hx
    · intro w hw
      simp [V0, V1] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P1ProfileSub, profileOnSubset, P1Ballots]
        exact ballotABCD_UpperSet_ab
      }
  have hy_mem : y ∈ f P1ProfileSub := by rw [hP1]; simp
  exact hsubset hy_mem

lemma P1_to_P2_preserve_a {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP1 : f P1ProfileSub = {0}) (hP2 : f P2ProfileSub = {y}) :
    y = 0 := by
  let S : Finset (Fin 4) := {1, 2, 3}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P1ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V2 V1 (by simp [V2, V1]; intro x hx; simp_all) P1ProfileSub S y
    · erw [restrictProfile_eq_profileOnSubset (hST := by simp [V2, V1]; intro x hx; simp_all)]
      exact hP2
    · exact hyS
    · intro w hw
      simp [V2, V1] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P1ProfileSub, profileOnSubset, P1Ballots]
        exact ballotBDCA_UpperSet_not_a
      }
  have h0_mem : (0 : Fin 4) ∈ f P1ProfileSub := by rw [hP1]; simp
  have h0S : (0 : Fin 4) ∈ S := hsubset h0_mem
  simp [S] at h0S

lemma P1_to_P3_preserve_b {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP1 : f P1ProfileSub = {1}) (hP3 : f P3ProfileSub = {y}) :
    y = 1 := by
  let S : Finset (Fin 4) := {0, 2, 3}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P1ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V3 V1 (by simp [V3, V1]; intro x hx; simp_all) P1ProfileSub S y
    · erw [restrictProfile_eq_profileOnSubset (hST := by simp [V3, V1]; intro x hx; simp_all)]
      exact hP3
    · exact hyS
    · intro w hw
      simp [V3, V1] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P1ProfileSub, profileOnSubset, P1Ballots]
        exact ballotDCAB_UpperSet_not_b
      }
  have h1_mem : (1 : Fin 4) ∈ f P1ProfileSub := by rw [hP1]; simp
  have h1S : (1 : Fin 4) ∈ S := hsubset h1_mem
  simp [S] at h1S

lemma P3_to_P4_preserve_bd {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP3 : f P3ProfileSub = {1}) (hP4 : f P4ProfileSub = {y}) :
    y ∈ ({1, 3} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {0, 2}
  by_contra hy
  have hyS : y ∈ S := by
    by_contra hy_not_S
    simp [S] at hy_not_S
    have hy_in : y ∈ ({1, 3} : Finset (Fin 4)) := by
      fin_cases y <;> simp at *
    contradiction
  have hsubset : f P3ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V4 V3 (by simp [V3, V4]; intro x hx; simp_all) P3ProfileSub S y
    · erw [restrictProfile_eq_profileOnSubset (hST := by simp [V3, V4]; intro x hx; simp_all)]
      exact hP4
    · exact hyS
    · intro w hw
      simp [V3, V4] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P3ProfileSub, profileOnSubset, P1Ballots]
        exact ballotCABD_UpperSet_ca
      }
  have h1_mem : (1 : Fin 4) ∈ f P3ProfileSub := by rw [hP3]; simp
  have h1S : (1 : Fin 4) ∈ S := hsubset h1_mem
  simp [S] at h1S

-- TODO: add the following lemmas, similar to the existing ones:
-- * P0 to P5 preserve cd
-- * P5 to P6 preserve d
-- * P5 to P6 preserve c
-- * P6 to P7 preserve ca

-- Condorcet Winners

set_option maxHeartbeats 1000000

lemma P2_condorcet_winner_c : CondorcetWinner P2ProfileSub 2 := by
  intro y hy
  fin_cases y
  · -- Case y = 0
    unfold StrictMajority votersPreferring
    simp [P2ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
          V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
          ListBallot.mk']
    decide
  · -- Case y = 1
    unfold StrictMajority votersPreferring
    simp [P2ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
          V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
          ListBallot.mk']
    decide
  · -- Case y = 2
    contradiction
  · -- Case y = 3
    unfold StrictMajority votersPreferring
    simp [P2ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
          V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
          ListBallot.mk']
    decide

lemma P4_condorcet_winner_a : CondorcetWinner P4ProfileSub 0 := by
  intro y hy
  fin_cases y
  · -- Case y = 0
    contradiction
  · -- Case y = 1
    unfold StrictMajority votersPreferring
    simp [P4ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
          V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
          ListBallot.mk']
    decide
  · -- Case y = 2
    unfold StrictMajority votersPreferring
    simp [P4ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
          V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
          ListBallot.mk']
    decide
  · -- Case y = 3
    unfold StrictMajority votersPreferring
    simp [P4ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
          V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
          ListBallot.mk']
    decide

-- TODO: add the following lemmas, similar to the existing ones:
-- * P6 condorcet winner b
-- * P8 condorcet winner d

-- Main Theorem

theorem no_resolute_condorcet_participation_m4_n12 :
    ¬ ∃ (f : VotingRule.{0,0}) (hf : Resolute f), CondorcetConsistency f ∧ ResoluteParticipation f hf := by
  rintro ⟨f, hf, hcond, hpart⟩
  -- P0 must have result {0} or {1} (a or b) w.l.o.g.
  have h_P0_res : (f P0ProfileSub).card = 1 := hf P0ProfileSub
  rcases Finset.card_eq_one.mp h_P0_res with ⟨x, hx⟩

  by_cases h_ab : x ∈ ({0, 1} : Finset (Fin 4))
  · -- Case x \in {a,b}
    have h_P1_res : (f P1ProfileSub).card = 1 := hf P1ProfileSub
    rcases Finset.card_eq_one.mp h_P1_res with ⟨y, hy⟩
    have hy_ab : y ∈ ({0, 1} : Finset (Fin 4)) :=
      P0_to_P1_preserve_ab hf hpart h_ab hx hy

    -- Split y = 0 or y = 1
    rw [Finset.mem_insert, Finset.mem_singleton] at hy_ab
    rcases hy_ab with (rfl | rfl)
    · -- y = 0 (a)
      -- Path to P2
      have h_P2_res : (f P2ProfileSub).card = 1 := hf P2ProfileSub
      rcases Finset.card_eq_one.mp h_P2_res with ⟨z, hz⟩
      have hz_eq : z = 0 := P1_to_P2_preserve_a hf hpart hy hz
      rw [hz_eq] at hz
      -- P2 has CW c (2). f(P2) = {a} (0).
      have h_cw : f P2ProfileSub = {2} := hcond P2ProfileSub 2 P2_condorcet_winner_c
      rw [hz] at h_cw
      have : (0 : Fin 4) = 2 := by
         have : 0 ∈ ({2} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      contradiction
    · -- y = 1 (b)
      -- Path to P3, then P4
      have h_P3_res : (f P3ProfileSub).card = 1 := hf P3ProfileSub
      rcases Finset.card_eq_one.mp h_P3_res with ⟨z, hz⟩
      have hz_eq : z = 1 := P1_to_P3_preserve_b hf hpart hy hz
      rw [hz_eq] at hz
      -- Path to P4
      have h_P4_res : (f P4ProfileSub).card = 1 := hf P4ProfileSub
      rcases Finset.card_eq_one.mp h_P4_res with ⟨w, hw⟩
      have hw_bd : w ∈ ({1, 3} : Finset (Fin 4)) :=
        P3_to_P4_preserve_bd hf hpart hz hw
      -- P4 has CW a (0). f(P4) = {w}. w \in {b, d}.
      have h_cw : f P4ProfileSub = {0} := hcond P4ProfileSub 0 P4_condorcet_winner_a
      rw [hw] at h_cw
      have : w = 0 := by
         have : w ∈ ({0} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      rw [this] at hw_bd
      simp at hw_bd -- 0 \in {1, 3} is False
  · -- Case x \in {c,d}
    sorry

end SocialChoice
