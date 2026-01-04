import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Participation
import SocialChoice.Examples
import Mathlib.Tactic

/-
This file contains a proof that no voting rule can satisfy
resoluteness, Condorcet consistency, and resolute participation
simultaneously. It works by analyzing several explicit profiles
with m=4 alternatvies and up to n=12 voters.

The proof follows the computer-aided proof of
Brandt et al. (2016), in the improved version presented
in Dominik Peters' 2019 DPhil thesis:
https://dominik-peters.de/publications/thesis.pdf#page=27
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

-- Generic profile definition on a subset of voters, using P5Ballots
noncomputable def profileOnSubsetP5 (S : Finset (Fin 12)) :
    Profile (Electorate (Fin 12) S) (Fin 4) :=
  { pref := fun v => (P5Ballots v.1).toLinearOrder }

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

noncomputable def P0ProfileSubP5 : Profile (Electorate (Fin 12) V0) (Fin 4) :=
  profileOnSubsetP5 V0

noncomputable def P5ProfileSub : Profile (Electorate (Fin 12) V5) (Fin 4) :=
  profileOnSubsetP5 V5

noncomputable def P6ProfileSub : Profile (Electorate (Fin 12) V6) (Fin 4) :=
  profileOnSubsetP5 V6

noncomputable def P7ProfileSub : Profile (Electorate (Fin 12) V7) (Fin 4) :=
  profileOnSubsetP5 V7

noncomputable def P8ProfileSub : Profile (Electorate (Fin 12) V8) (Fin 4) :=
  profileOnSubsetP5 V8

-- Lemma for restrictProfile equality for P5
lemma restrictProfile_eq_profileOnSubsetP5 {S T : Finset (Fin 12)} (hST : S ⊆ T) :
    restrictProfile (profileOnSubsetP5 T) S hST = profileOnSubsetP5 S := by
  simp [restrictProfile, profileOnSubsetP5]

lemma P0_P5_coincide : P0ProfileSub = P0ProfileSubP5 := by
  simp [P0ProfileSub, P0ProfileSubP5, profileOnSubset, profileOnSubsetP5]
  ext v
  fin_cases v <;> simp [P1Ballots, P5Ballots]

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

lemma P0_to_P5_preserve_cd {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({2, 3} : Finset (Fin 4)))
    (hP0 : f P0ProfileSubP5 = {x}) (hP5 : f P5ProfileSub = {y}) :
    y ∈ ({2, 3} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {2, 3}
  have hVW : V0 ⊆ V5 := by
    intro z hz
    simp [V0, V5] at hz ⊢
    tauto
  have hsubset : f P5ProfileSub ⊆ S := by
    refine resoluteParticipation_superset hf hpart V0 V5 hVW P5ProfileSub S x ?hx ?hxS ?hUpper
    · erw [restrictProfile_eq_profileOnSubsetP5 (hST := hVW)]
      exact hP0
    · simpa [S] using hx
    · intro w hw
      simp [V0, V5] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P5ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotDCBA_UpperSet_dc
      }
  have hy_mem : y ∈ f P5ProfileSub := by rw [hP5]; simp
  exact hsubset hy_mem

lemma P5_to_P6_preserve_d {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP5 : f P5ProfileSub = {3}) (hP6 : f P6ProfileSub = {y}) :
    y = 3 := by
  let S : Finset (Fin 4) := {0, 1, 2}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P5ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V6 V5 (by simp [V6, V5]; intro x hx; simp_all) P5ProfileSub S y
    · erw [restrictProfile_eq_profileOnSubsetP5 (hST := by simp [V6, V5]; intro x hx; simp_all)]
      exact hP6
    · exact hyS
    · intro w hw
      simp [V6, V5] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P5ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotCABD_UpperSet_not_d
      }
  have h3_mem : (3 : Fin 4) ∈ f P5ProfileSub := by rw [hP5]; simp
  have h3S : (3 : Fin 4) ∈ S := hsubset h3_mem
  simp [S] at h3S

lemma P5_to_P7_preserve_c {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP5 : f P5ProfileSub = {2}) (hP7 : f P7ProfileSub = {y}) :
    y = 2 := by
  let S : Finset (Fin 4) := {0, 1, 3}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P5ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V7 V5 (by simp [V7, V5]; intro x hx; simp_all) P5ProfileSub S y
    · erw [restrictProfile_eq_profileOnSubsetP5 (hST := by simp [V7, V5]; intro x hx; simp_all)]
      exact hP7
    · exact hyS
    · intro w hw
      simp [V7, V5] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P5ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotABDC_UpperSet_not_c
      }
  have h2_mem : (2 : Fin 4) ∈ f P5ProfileSub := by rw [hP5]; simp
  have h2S : (2 : Fin 4) ∈ S := hsubset h2_mem
  simp [S] at h2S

lemma P7_to_P8_preserve_ac {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP7 : f P7ProfileSub = {2}) (hP8 : f P8ProfileSub = {y}) :
    y ∈ ({0, 2} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {1, 3}
  by_contra hy
  have hyS : y ∈ S := by
    by_contra hy_not_S
    simp [S] at hy_not_S
    have hy_in : y ∈ ({0, 2} : Finset (Fin 4)) := by
      fin_cases y <;> simp at *
    contradiction
  have hsubset : f P7ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V8 V7 (by simp [V7, V8]; intro x hx; simp_all) P7ProfileSub S y
    · erw [restrictProfile_eq_profileOnSubsetP5 (hST := by simp [V7, V8]; intro x hx; simp_all)]
      exact hP8
    · exact hyS
    · intro w hw
      simp [V7, V8] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P7ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotBDCA_UpperSet_bd
      }
  have h2_mem : (2 : Fin 4) ∈ f P7ProfileSub := by rw [hP7]; simp
  have h2S : (2 : Fin 4) ∈ S := hsubset h2_mem
  simp [S] at h2S

-- Condorcet winners for the four key profiles.

@[simp] private lemma P2_strict_majority_0 : StrictMajority (votersPreferring P2ProfileSub 2 0) := by
  unfold StrictMajority votersPreferring
  simp [P2ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
        V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
        ListBallot.mk']
  decide

@[simp] private lemma P2_strict_majority_1 : StrictMajority (votersPreferring P2ProfileSub 2 1) := by
  unfold StrictMajority votersPreferring
  simp [P2ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
        V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
        ListBallot.mk']
  decide

@[simp] private lemma P2_strict_majority_3 : StrictMajority (votersPreferring P2ProfileSub 2 3) := by
  unfold StrictMajority votersPreferring
  simp [P2ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
        V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
        ListBallot.mk']
  decide

@[simp] private lemma P4_strict_majority_1 : StrictMajority (votersPreferring P4ProfileSub 0 1) := by
  unfold StrictMajority votersPreferring
  simp [P4ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
        V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
        ListBallot.mk']
  decide

@[simp] private lemma P4_strict_majority_2 : StrictMajority (votersPreferring P4ProfileSub 0 2) := by
  unfold StrictMajority votersPreferring
  simp [P4ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
        V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
        ListBallot.mk']
  decide

@[simp] private lemma P4_strict_majority_3 : StrictMajority (votersPreferring P4ProfileSub 0 3) := by
  unfold StrictMajority votersPreferring
  simp [P4ProfileSub, profileOnSubset, Prefers, ListBallot.lt_iff_idxOf,
        V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
        ListBallot.mk']
  decide

@[simp] private lemma P6_strict_majority_0 : StrictMajority (votersPreferring P6ProfileSub 1 0) := by
  unfold StrictMajority votersPreferring
  simp [P6ProfileSub, profileOnSubsetP5, Prefers, ListBallot.lt_iff_idxOf,
        V6, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
        ListBallot.mk']
  decide

@[simp] private lemma P6_strict_majority_2 : StrictMajority (votersPreferring P6ProfileSub 1 2) := by
  unfold StrictMajority votersPreferring
  simp [P6ProfileSub, profileOnSubsetP5, Prefers, ListBallot.lt_iff_idxOf,
        V6, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
        ListBallot.mk']
  decide

@[simp] private lemma P6_strict_majority_3 : StrictMajority (votersPreferring P6ProfileSub 1 3) := by
  unfold StrictMajority votersPreferring
  simp [P6ProfileSub, profileOnSubsetP5, Prefers, ListBallot.lt_iff_idxOf,
        V6, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
        ListBallot.mk']
  decide

@[simp] private lemma P8_strict_majority_0 : StrictMajority (votersPreferring P8ProfileSub 3 0) := by
  unfold StrictMajority votersPreferring
  simp [P8ProfileSub, profileOnSubsetP5, Prefers, ListBallot.lt_iff_idxOf,
        V8, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
        ListBallot.mk']
  decide

@[simp] private lemma P8_strict_majority_1 : StrictMajority (votersPreferring P8ProfileSub 3 1) := by
  unfold StrictMajority votersPreferring
  simp [P8ProfileSub, profileOnSubsetP5, Prefers, ListBallot.lt_iff_idxOf,
        V8, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
        ListBallot.mk']
  decide

@[simp] private lemma P8_strict_majority_2 : StrictMajority (votersPreferring P8ProfileSub 3 2) := by
  unfold StrictMajority votersPreferring
  simp [P8ProfileSub, profileOnSubsetP5, Prefers, ListBallot.lt_iff_idxOf,
        V8, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
        ListBallot.mk']
  decide

lemma P2_condorcet_winner_c : CondorcetWinner P2ProfileSub 2 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma P4_condorcet_winner_a : CondorcetWinner P4ProfileSub 0 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma P6_condorcet_winner_b : CondorcetWinner P6ProfileSub 1 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma P8_condorcet_winner_d : CondorcetWinner P8ProfileSub 3 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

-- Main Theorem

theorem no_resolute_condorcet_participation_m4_n12 :
    ¬ ∃ (f : VotingRule) (hf : Resolute f), CondorcetConsistency f ∧ ResoluteParticipation f hf := by
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
    -- Switch to P5 world
    have h_P0_res_P5 : (f P0ProfileSubP5).card = 1 := by rw [← P0_P5_coincide]; exact h_P0_res
    -- Since P0ProfileSub = P0ProfileSubP5, f(P0) is same.
    rw [P0_P5_coincide] at hx

    have hx_cd : x ∈ ({2, 3} : Finset (Fin 4)) := by
      simp at h_ab
      fin_cases x <;> simp at *

    have h_P5_res : (f P5ProfileSub).card = 1 := hf P5ProfileSub
    rcases Finset.card_eq_one.mp h_P5_res with ⟨y, hy⟩
    have hy_cd : y ∈ ({2, 3} : Finset (Fin 4)) :=
      P0_to_P5_preserve_cd hf hpart hx_cd hx hy

    rw [Finset.mem_insert, Finset.mem_singleton] at hy_cd
    rcases hy_cd with (rfl | rfl)
    · -- y = 2 (c)
      -- Path to P7, then P8
      have h_P7_res : (f P7ProfileSub).card = 1 := hf P7ProfileSub
      rcases Finset.card_eq_one.mp h_P7_res with ⟨z, hz⟩
      have hz_eq : z = 2 := P5_to_P7_preserve_c hf hpart hy hz
      rw [hz_eq] at hz
      -- Path to P8
      have h_P8_res : (f P8ProfileSub).card = 1 := hf P8ProfileSub
      rcases Finset.card_eq_one.mp h_P8_res with ⟨w, hw⟩
      have hw_ac : w ∈ ({0, 2} : Finset (Fin 4)) :=
        P7_to_P8_preserve_ac hf hpart hz hw
      -- P8 has CW d (3). f(P8) = {w}. w \in {a, c}.
      have h_cw : f P8ProfileSub = {3} := hcond P8ProfileSub 3 P8_condorcet_winner_d
      rw [hw] at h_cw
      have : w = 3 := by
         have : w ∈ ({3} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      rw [this] at hw_ac
      simp at hw_ac -- 3 \in {0, 2} is False
    · -- y = 3 (d)
      -- Path to P6
      have h_P6_res : (f P6ProfileSub).card = 1 := hf P6ProfileSub
      rcases Finset.card_eq_one.mp h_P6_res with ⟨z, hz⟩
      have hz_eq : z = 3 := P5_to_P6_preserve_d hf hpart hy hz
      rw [hz_eq] at hz
      -- P6 has CW b (1). f(P6) = {d} (3).
      have h_cw : f P6ProfileSub = {1} := hcond P6ProfileSub 1 P6_condorcet_winner_b
      rw [hz] at h_cw
      have : (3 : Fin 4) = 1 := by
         have : 3 ∈ ({1} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      contradiction

end SocialChoice
