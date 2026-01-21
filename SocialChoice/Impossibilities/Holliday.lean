import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Fin
import SocialChoice.Profile
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Margin

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

/-! Basic scaffolding for Holliday impossibility (5 candidates). -/

abbrev A5 := Fin 5

abbrev a : A5 := 0
abbrev b : A5 := 1
abbrev c : A5 := 2
abbrev d : A5 := 3
abbrev e : A5 := 4

-- Ballots from Figure 1 in holliday_impossibility.tex.
def ballot_acdeb : ListBallot 5 := ListBallot.mk' [a, c, d, e, b]
def ballot_baced : ListBallot 5 := ListBallot.mk' [b, a, c, e, d]
def ballot_ebdca : ListBallot 5 := ListBallot.mk' [e, b, d, c, a]
def ballot_bacde : ListBallot 5 := ListBallot.mk' [b, a, c, d, e]
def ballot_cebda : ListBallot 5 := ListBallot.mk' [c, e, b, d, a]
def ballot_edbac : ListBallot 5 := ListBallot.mk' [e, d, b, a, c]
def ballot_edcba : ListBallot 5 := ListBallot.mk' [e, d, c, b, a]
def ballot_dacbe : ListBallot 5 := ListBallot.mk' [d, a, c, b, e]
def ballot_dceba : ListBallot 5 := ListBallot.mk' [d, c, e, b, a]
def ballot_daecb : ListBallot 5 := ListBallot.mk' [d, a, e, c, b]
def ballot_bdace : ListBallot 5 := ListBallot.mk' [b, d, a, c, e]
def ballot_aecbd : ListBallot 5 := ListBallot.mk' [a, e, c, b, d]
def ballot_adbec : ListBallot 5 := ListBallot.mk' [a, d, b, e, c]
def ballot_bdeca : ListBallot 5 := ListBallot.mk' [b, d, e, c, a]

/-! Block lists for margins (order matches the table in Figure 1). -/

def blocksP1 : List (Nat × ListBallot 5) :=
  [(63, ballot_acdeb), (39, ballot_baced), (35, ballot_ebdca), (24, ballot_bacde),
   (21, ballot_cebda), (22, ballot_edbac), (11, ballot_edcba), (10, ballot_dacbe),
   (14, ballot_dceba), (8, ballot_daecb), (6, ballot_bdace), (4, ballot_aecbd)]

def blocksP2 : List (Nat × ListBallot 5) :=
  blocksP1 ++ [(28, ballot_adbec)]

def blocksP3 : List (Nat × ListBallot 5) :=
  [(63, ballot_acdeb), (39, ballot_baced), (35, ballot_ebdca), (24, ballot_bacde),
   (21, ballot_cebda), (22, ballot_edbac), (11, ballot_edcba), (10, ballot_dacbe),
   (14, ballot_dceba), (8, ballot_daecb), (4, ballot_aecbd), (28, ballot_adbec)]

def blocksP4 : List (Nat × ListBallot 5) :=
  blocksP3 ++ [(26, ballot_bdeca)]

def blocksP5 : List (Nat × ListBallot 5) :=
  [(63, ballot_acdeb), (39, ballot_baced), (35, ballot_ebdca), (24, ballot_bacde),
   (21, ballot_cebda), (22, ballot_edbac), (11, ballot_edcba), (10, ballot_dacbe),
   (8, ballot_daecb), (4, ballot_aecbd), (28, ballot_adbec), (26, ballot_bdeca)]

/-! ### P1 on a single electorate (Fin 311) -/

abbrev U311 := Fin 311

def p1_cut1 : Nat := 63
def p1_cut2 : Nat := 102
def p1_cut3 : Nat := 137
def p1_cut4 : Nat := 161
def p1_cut5 : Nat := 182
def p1_cut6 : Nat := 204
def p1_cut7 : Nat := 215
def p1_cut8 : Nat := 225
def p1_cut9 : Nat := 239
def p1_cut10 : Nat := 247
def p1_cut11 : Nat := 253
def p1_cut12 : Nat := 257
def p1_cut13 : Nat := 285
def p1_cut14 : Nat := 311

lemma p1_cut1_le_cut2 : p1_cut1 ≤ p1_cut2 := by decide
lemma p1_cut2_le_cut3 : p1_cut2 ≤ p1_cut3 := by decide
lemma p1_cut3_le_cut4 : p1_cut3 ≤ p1_cut4 := by decide
lemma p1_cut4_le_cut5 : p1_cut4 ≤ p1_cut5 := by decide
lemma p1_cut5_le_cut6 : p1_cut5 ≤ p1_cut6 := by decide
lemma p1_cut6_le_cut7 : p1_cut6 ≤ p1_cut7 := by decide
lemma p1_cut7_le_cut8 : p1_cut7 ≤ p1_cut8 := by decide
lemma p1_cut8_le_cut9 : p1_cut8 ≤ p1_cut9 := by decide
lemma p1_cut9_le_cut10 : p1_cut9 ≤ p1_cut10 := by decide
lemma p1_cut10_le_cut11 : p1_cut10 ≤ p1_cut11 := by decide
lemma p1_cut11_le_cut12 : p1_cut11 ≤ p1_cut12 := by decide
lemma p1_cut12_le_cut13 : p1_cut12 ≤ p1_cut13 := by decide
lemma p1_cut13_le_cut14 : p1_cut13 ≤ p1_cut14 := by decide

def p1_cut1_fin : U311 := ⟨p1_cut1, by decide⟩
def p1_cut2_fin : U311 := ⟨p1_cut2, by decide⟩
def p1_cut3_fin : U311 := ⟨p1_cut3, by decide⟩
def p1_cut4_fin : U311 := ⟨p1_cut4, by decide⟩
def p1_cut5_fin : U311 := ⟨p1_cut5, by decide⟩
def p1_cut6_fin : U311 := ⟨p1_cut6, by decide⟩
def p1_cut7_fin : U311 := ⟨p1_cut7, by decide⟩
def p1_cut8_fin : U311 := ⟨p1_cut8, by decide⟩
def p1_cut9_fin : U311 := ⟨p1_cut9, by decide⟩
def p1_cut10_fin : U311 := ⟨p1_cut10, by decide⟩
def p1_cut11_fin : U311 := ⟨p1_cut11, by decide⟩
def p1_cut12_fin : U311 := ⟨p1_cut12, by decide⟩
def p1_cut13_fin : U311 := ⟨p1_cut13, by decide⟩

def votersP1_1 : Finset U311 :=
  Finset.univ.filter (fun v => v.val < p1_cut1)

def votersP1_2 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut1 ≤ v.val ∧ v.val < p1_cut2)

def votersP1_3 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut2 ≤ v.val ∧ v.val < p1_cut3)

def votersP1_4 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut3 ≤ v.val ∧ v.val < p1_cut4)

def votersP1_5 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut4 ≤ v.val ∧ v.val < p1_cut5)

def votersP1_6 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut5 ≤ v.val ∧ v.val < p1_cut6)

def votersP1_7 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut6 ≤ v.val ∧ v.val < p1_cut7)

def votersP1_8 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut7 ≤ v.val ∧ v.val < p1_cut8)

def votersP1_9 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut8 ≤ v.val ∧ v.val < p1_cut9)

def votersP1_10 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut9 ≤ v.val ∧ v.val < p1_cut10)

def votersP1_11 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut10 ≤ v.val ∧ v.val < p1_cut11)

def votersP1_12 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut11 ≤ v.val ∧ v.val < p1_cut12)

def votersP1_13 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut12 ≤ v.val ∧ v.val < p1_cut13)

def votersP1_14 : Finset U311 :=
  Finset.univ.filter (fun v => p1_cut13 ≤ v.val ∧ v.val < p1_cut14)

lemma mem_votersP1_1_iff (v : U311) : v ∈ votersP1_1 ↔ v.val < p1_cut1 := by
  simp [votersP1_1]

lemma mem_votersP1_2_iff (v : U311) :
    v ∈ votersP1_2 ↔ p1_cut1 ≤ v.val ∧ v.val < p1_cut2 := by
  simp [votersP1_2]

lemma mem_votersP1_3_iff (v : U311) :
    v ∈ votersP1_3 ↔ p1_cut2 ≤ v.val ∧ v.val < p1_cut3 := by
  simp [votersP1_3]

lemma mem_votersP1_4_iff (v : U311) :
    v ∈ votersP1_4 ↔ p1_cut3 ≤ v.val ∧ v.val < p1_cut4 := by
  simp [votersP1_4]

lemma mem_votersP1_5_iff (v : U311) :
    v ∈ votersP1_5 ↔ p1_cut4 ≤ v.val ∧ v.val < p1_cut5 := by
  simp [votersP1_5]

lemma mem_votersP1_6_iff (v : U311) :
    v ∈ votersP1_6 ↔ p1_cut5 ≤ v.val ∧ v.val < p1_cut6 := by
  simp [votersP1_6]

lemma mem_votersP1_7_iff (v : U311) :
    v ∈ votersP1_7 ↔ p1_cut6 ≤ v.val ∧ v.val < p1_cut7 := by
  simp [votersP1_7]

lemma mem_votersP1_8_iff (v : U311) :
    v ∈ votersP1_8 ↔ p1_cut7 ≤ v.val ∧ v.val < p1_cut8 := by
  simp [votersP1_8]

lemma mem_votersP1_9_iff (v : U311) :
    v ∈ votersP1_9 ↔ p1_cut8 ≤ v.val ∧ v.val < p1_cut9 := by
  simp [votersP1_9]

lemma mem_votersP1_10_iff (v : U311) :
    v ∈ votersP1_10 ↔ p1_cut9 ≤ v.val ∧ v.val < p1_cut10 := by
  simp [votersP1_10]

lemma mem_votersP1_11_iff (v : U311) :
    v ∈ votersP1_11 ↔ p1_cut10 ≤ v.val ∧ v.val < p1_cut11 := by
  simp [votersP1_11]

lemma mem_votersP1_12_iff (v : U311) :
    v ∈ votersP1_12 ↔ p1_cut11 ≤ v.val ∧ v.val < p1_cut12 := by
  simp [votersP1_12]

lemma mem_votersP1_13_iff (v : U311) :
    v ∈ votersP1_13 ↔ p1_cut12 ≤ v.val ∧ v.val < p1_cut13 := by
  simp [votersP1_13]

lemma mem_votersP1_14_iff (v : U311) :
    v ∈ votersP1_14 ↔ p1_cut13 ≤ v.val ∧ v.val < p1_cut14 := by
  simp [votersP1_14]

lemma votersP1_1_eq_Ico : votersP1_1 = Finset.Ico 0 p1_cut1_fin := by
  ext v
  simp [votersP1_1, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut1_fin]

lemma votersP1_2_eq_Ico : votersP1_2 = Finset.Ico p1_cut1_fin p1_cut2_fin := by
  ext v
  simp [votersP1_2, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut1_fin, p1_cut2_fin]

lemma votersP1_3_eq_Ico : votersP1_3 = Finset.Ico p1_cut2_fin p1_cut3_fin := by
  ext v
  simp [votersP1_3, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut2_fin, p1_cut3_fin]

lemma votersP1_4_eq_Ico : votersP1_4 = Finset.Ico p1_cut3_fin p1_cut4_fin := by
  ext v
  simp [votersP1_4, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut3_fin, p1_cut4_fin]

lemma votersP1_5_eq_Ico : votersP1_5 = Finset.Ico p1_cut4_fin p1_cut5_fin := by
  ext v
  simp [votersP1_5, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut4_fin, p1_cut5_fin]

lemma votersP1_6_eq_Ico : votersP1_6 = Finset.Ico p1_cut5_fin p1_cut6_fin := by
  ext v
  simp [votersP1_6, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut5_fin, p1_cut6_fin]

lemma votersP1_7_eq_Ico : votersP1_7 = Finset.Ico p1_cut6_fin p1_cut7_fin := by
  ext v
  simp [votersP1_7, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut6_fin, p1_cut7_fin]

lemma votersP1_8_eq_Ico : votersP1_8 = Finset.Ico p1_cut7_fin p1_cut8_fin := by
  ext v
  simp [votersP1_8, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut7_fin, p1_cut8_fin]

lemma votersP1_9_eq_Ico : votersP1_9 = Finset.Ico p1_cut8_fin p1_cut9_fin := by
  ext v
  simp [votersP1_9, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin, p1_cut9_fin]

lemma votersP1_10_eq_Ico : votersP1_10 = Finset.Ico p1_cut9_fin p1_cut10_fin := by
  ext v
  simp [votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut9_fin, p1_cut10_fin]

lemma votersP1_11_eq_Ico : votersP1_11 = Finset.Ico p1_cut10_fin p1_cut11_fin := by
  ext v
  simp [votersP1_11, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut10_fin, p1_cut11_fin]

lemma votersP1_12_eq_Ico : votersP1_12 = Finset.Ico p1_cut11_fin p1_cut12_fin := by
  ext v
  simp [votersP1_12, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut11_fin, p1_cut12_fin]

lemma votersP1_13_eq_Ico : votersP1_13 = Finset.Ico p1_cut12_fin p1_cut13_fin := by
  ext v
  simp [votersP1_13, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut12_fin, p1_cut13_fin]

lemma votersP1_14_eq_Ici : votersP1_14 = Finset.Ici p1_cut13_fin := by
  ext v
  have hv : v.val < p1_cut14 := by
    exact v.2
  constructor
  · intro hv'
    rcases (mem_votersP1_14_iff v).1 hv' with ⟨hlo, _hhi⟩
    simpa [Finset.mem_Ici, Fin.le_def, p1_cut13_fin] using hlo
  · intro hv'
    have hlo : p1_cut13 ≤ v.val := by
      simpa [Finset.mem_Ici, Fin.le_def, p1_cut13_fin] using hv'
    exact (mem_votersP1_14_iff v).2 ⟨hlo, hv⟩

lemma card_votersP1_1 : votersP1_1.card = 63 := by
  simp [votersP1_1_eq_Ico, p1_cut1_fin, p1_cut1]

lemma card_votersP1_2 : votersP1_2.card = 39 := by
  simp [votersP1_2_eq_Ico, p1_cut1_fin, p1_cut2_fin, p1_cut1, p1_cut2]

lemma card_votersP1_3 : votersP1_3.card = 35 := by
  simp [votersP1_3_eq_Ico, p1_cut2_fin, p1_cut3_fin, p1_cut2, p1_cut3]

lemma card_votersP1_4 : votersP1_4.card = 24 := by
  simp [votersP1_4_eq_Ico, p1_cut3_fin, p1_cut4_fin, p1_cut3, p1_cut4]

lemma card_votersP1_5 : votersP1_5.card = 21 := by
  simp [votersP1_5_eq_Ico, p1_cut4_fin, p1_cut5_fin, p1_cut4, p1_cut5]

lemma card_votersP1_6 : votersP1_6.card = 22 := by
  simp [votersP1_6_eq_Ico, p1_cut5_fin, p1_cut6_fin, p1_cut5, p1_cut6]

lemma card_votersP1_7 : votersP1_7.card = 11 := by
  simp [votersP1_7_eq_Ico, p1_cut6_fin, p1_cut7_fin, p1_cut6, p1_cut7]

lemma card_votersP1_8 : votersP1_8.card = 10 := by
  simp [votersP1_8_eq_Ico, p1_cut7_fin, p1_cut8_fin, p1_cut7, p1_cut8]

lemma card_votersP1_9 : votersP1_9.card = 14 := by
  simp [votersP1_9_eq_Ico, p1_cut8_fin, p1_cut9_fin, p1_cut8, p1_cut9]

lemma card_votersP1_10 : votersP1_10.card = 8 := by
  simp [votersP1_10_eq_Ico, p1_cut9_fin, p1_cut10_fin, p1_cut9, p1_cut10]

lemma card_votersP1_11 : votersP1_11.card = 6 := by
  simp [votersP1_11_eq_Ico, p1_cut10_fin, p1_cut11_fin, p1_cut10, p1_cut11]

lemma card_votersP1_12 : votersP1_12.card = 4 := by
  simp [votersP1_12_eq_Ico, p1_cut11_fin, p1_cut12_fin, p1_cut11, p1_cut12]

lemma card_votersP1_13 : votersP1_13.card = 28 := by
  simp [votersP1_13_eq_Ico, p1_cut12_fin, p1_cut13_fin, p1_cut12, p1_cut13]

lemma card_votersP1_14 : votersP1_14.card = 26 := by
  simp [votersP1_14_eq_Ici, p1_cut13_fin, p1_cut13]

def ballotsAllCuts : List (Nat × ListBallot 5) :=
  [(p1_cut1, ballot_acdeb), (p1_cut2, ballot_baced), (p1_cut3, ballot_ebdca),
   (p1_cut4, ballot_bacde), (p1_cut5, ballot_cebda), (p1_cut6, ballot_edbac),
   (p1_cut7, ballot_edcba), (p1_cut8, ballot_dacbe), (p1_cut9, ballot_dceba),
   (p1_cut10, ballot_daecb), (p1_cut11, ballot_bdace), (p1_cut12, ballot_aecbd),
   (p1_cut13, ballot_adbec), (p1_cut14, ballot_bdeca)]

def ballotByCuts : List (Nat × ListBallot 5) → Nat → ListBallot 5
  | [], _ => ballot_bdeca
  | (cut, ballot) :: tail, n => if n < cut then ballot else ballotByCuts tail n

lemma ballotByCuts_eq_of_lt {cut : Nat} {ballot : ListBallot 5} {tail : List (Nat × ListBallot 5)}
    {n : Nat} (h : n < cut) :
    ballotByCuts ((cut, ballot) :: tail) n = ballot := by
  simp [ballotByCuts, h]

lemma ballotByCuts_eq_of_ge {cut : Nat} {ballot : ListBallot 5} {tail : List (Nat × ListBallot 5)}
    {n : Nat} (h : cut ≤ n) :
    ballotByCuts ((cut, ballot) :: tail) n = ballotByCuts tail n := by
  simp [ballotByCuts, not_lt_of_ge h]

noncomputable def ballotsAll (v : U311) : ListBallot 5 :=
  ballotByCuts ballotsAllCuts v.val

lemma ballotsAll_eq_ballot_acdeb_of_mem_votersP1_1 {v : U311} (hv : v ∈ votersP1_1) :
    ballotsAll v = ballot_acdeb := by
  have hv' : v.val < p1_cut1 := (mem_votersP1_1_iff v).1 hv
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hv']

lemma ballotsAll_eq_ballot_baced_of_mem_votersP1_2 {v : U311} (hv : v ∈ votersP1_2) :
    ballotsAll v = ballot_baced := by
  have hv' := (mem_votersP1_2_iff v).1 hv
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hv'.2]

lemma ballotsAll_eq_ballot_ebdca_of_mem_votersP1_3 {v : U311} (hv : v ∈ votersP1_3) :
    ballotsAll v = ballot_ebdca := by
  have hv' := (mem_votersP1_3_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val := le_trans p1_cut1_le_cut2 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hv'.2]

lemma ballotsAll_eq_ballot_bacde_of_mem_votersP1_4 {v : U311} (hv : v ∈ votersP1_4) :
    ballotsAll v = ballot_bacde := by
  have hv' := (mem_votersP1_4_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3 hv'.1)
  have hge2 : p1_cut2 ≤ v.val := le_trans p1_cut2_le_cut3 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hv'.2]

lemma ballotsAll_eq_ballot_cebda_of_mem_votersP1_5 {v : U311} (hv : v ∈ votersP1_5) :
    ballotsAll v = ballot_cebda := by
  have hv' := (mem_votersP1_5_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4 hv'.1))
  have hge2 : p1_cut2 ≤ v.val := le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4 hv'.1)
  have hge3 : p1_cut3 ≤ v.val := le_trans p1_cut3_le_cut4 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hv'.2]

lemma ballotsAll_eq_ballot_edbac_of_mem_votersP1_6 {v : U311} (hv : v ∈ votersP1_6) :
    ballotsAll v = ballot_edbac := by
  have hv' := (mem_votersP1_6_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5 hv'.1)))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5 hv'.1))
  have hge3 : p1_cut3 ≤ v.val := le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5 hv'.1)
  have hge4 : p1_cut4 ≤ v.val := le_trans p1_cut4_le_cut5 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hv'.2]

lemma ballotsAll_eq_ballot_edcba_of_mem_votersP1_7 {v : U311} (hv : v ∈ votersP1_7) :
    ballotsAll v = ballot_edcba := by
  have hv' := (mem_votersP1_7_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 hv'.1))))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4
      (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 hv'.1)))
  have hge3 : p1_cut3 ≤ v.val :=
    le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 hv'.1))
  have hge4 : p1_cut4 ≤ v.val := le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 hv'.1)
  have hge5 : p1_cut5 ≤ v.val := le_trans p1_cut5_le_cut6 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hge5
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hv'.2]

lemma ballotsAll_eq_ballot_dacbe_of_mem_votersP1_8 {v : U311} (hv : v ∈ votersP1_8) :
    ballotsAll v = ballot_dacbe := by
  have hv' := (mem_votersP1_8_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
        (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 hv'.1)))))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4
      (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 hv'.1))))
  have hge3 : p1_cut3 ≤ v.val :=
    le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
      (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 hv'.1)))
  have hge4 : p1_cut4 ≤ v.val :=
    le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 hv'.1))
  have hge5 : p1_cut5 ≤ v.val := le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 hv'.1)
  have hge6 : p1_cut6 ≤ v.val := le_trans p1_cut6_le_cut7 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hge5
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge hge6
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hv'.2]

lemma ballotsAll_eq_ballot_dceba_of_mem_votersP1_9 {v : U311} (hv : v ∈ votersP1_9) :
    ballotsAll v = ballot_dceba := by
  have hv' := (mem_votersP1_9_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
        (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
          (le_trans p1_cut7_le_cut8 hv'.1))))))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4
      (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
        (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 hv'.1)))))
  have hge3 : p1_cut3 ≤ v.val :=
    le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
      (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 hv'.1))))
  have hge4 : p1_cut4 ≤ v.val :=
    le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
      (le_trans p1_cut7_le_cut8 hv'.1)))
  have hge5 : p1_cut5 ≤ v.val :=
    le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 hv'.1))
  have hge6 : p1_cut6 ≤ v.val := le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 hv'.1)
  have hge7 : p1_cut7 ≤ v.val := le_trans p1_cut7_le_cut8 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hge5
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge hge6
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge hge7
  have hnot8 : ¬ v.val < p1_cut8 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hnot8, hv'.2]

lemma ballotsAll_eq_ballot_daecb_of_mem_votersP1_10 {v : U311} (hv : v ∈ votersP1_10) :
    ballotsAll v = ballot_daecb := by
  have hv' := (mem_votersP1_10_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
        (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
          (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 hv'.1)))))))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4
      (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
        (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8
          (le_trans p1_cut8_le_cut9 hv'.1))))))
  have hge3 : p1_cut3 ≤ v.val :=
    le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
      (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
        (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 hv'.1)))))
  have hge4 : p1_cut4 ≤ v.val :=
    le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
      (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 hv'.1))))
  have hge5 : p1_cut5 ≤ v.val :=
    le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
      (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 hv'.1)))
  have hge6 : p1_cut6 ≤ v.val :=
    le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 hv'.1))
  have hge7 : p1_cut7 ≤ v.val := le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 hv'.1)
  have hge8 : p1_cut8 ≤ v.val := le_trans p1_cut8_le_cut9 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hge5
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge hge6
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge hge7
  have hnot8 : ¬ v.val < p1_cut8 := by
    exact not_lt_of_ge hge8
  have hnot9 : ¬ v.val < p1_cut9 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hnot8, hnot9, hv'.2]

lemma ballotsAll_eq_ballot_bdace_of_mem_votersP1_11 {v : U311} (hv : v ∈ votersP1_11) :
    ballotsAll v = ballot_bdace := by
  have hv' := (mem_votersP1_11_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
        (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
          (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9
            (le_trans p1_cut9_le_cut10 hv'.1))))))))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4
      (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
        (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8
          (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 hv'.1)))))))
  have hge3 : p1_cut3 ≤ v.val :=
    le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
      (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
        (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9
          (le_trans p1_cut9_le_cut10 hv'.1))))))
  have hge4 : p1_cut4 ≤ v.val :=
    le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
      (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8
        (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 hv'.1)))))
  have hge5 : p1_cut5 ≤ v.val :=
    le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
      (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 hv'.1))))
  have hge6 : p1_cut6 ≤ v.val :=
    le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9
      (le_trans p1_cut9_le_cut10 hv'.1)))
  have hge7 : p1_cut7 ≤ v.val :=
    le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 hv'.1))
  have hge8 : p1_cut8 ≤ v.val := le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 hv'.1)
  have hge9 : p1_cut9 ≤ v.val := le_trans p1_cut9_le_cut10 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hge5
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge hge6
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge hge7
  have hnot8 : ¬ v.val < p1_cut8 := by
    exact not_lt_of_ge hge8
  have hnot9 : ¬ v.val < p1_cut9 := by
    exact not_lt_of_ge hge9
  have hnot10 : ¬ v.val < p1_cut10 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hnot8, hnot9, hnot10, hv'.2]

lemma ballotsAll_eq_ballot_aecbd_of_mem_votersP1_12 {v : U311} (hv : v ∈ votersP1_12) :
    ballotsAll v = ballot_aecbd := by
  have hv' := (mem_votersP1_12_iff v).1 hv
  have hge1 : p1_cut1 ≤ v.val :=
    le_trans p1_cut1_le_cut2 (le_trans p1_cut2_le_cut3
      (le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
        (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
          (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9
            (le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1)))))))))
  have hge2 : p1_cut2 ≤ v.val :=
    le_trans p1_cut2_le_cut3 (le_trans p1_cut3_le_cut4
      (le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
        (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8
          (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10
            (le_trans p1_cut10_le_cut11 hv'.1))))))))
  have hge3 : p1_cut3 ≤ v.val :=
    le_trans p1_cut3_le_cut4 (le_trans p1_cut4_le_cut5
      (le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
        (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9
          (le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1)))))))
  have hge4 : p1_cut4 ≤ v.val :=
    le_trans p1_cut4_le_cut5 (le_trans p1_cut5_le_cut6
      (le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8
        (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1))))))
  have hge5 : p1_cut5 ≤ v.val :=
    le_trans p1_cut5_le_cut6 (le_trans p1_cut6_le_cut7
      (le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9
        (le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1)))))
  have hge6 : p1_cut6 ≤ v.val :=
    le_trans p1_cut6_le_cut7 (le_trans p1_cut7_le_cut8
      (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1))))
  have hge7 : p1_cut7 ≤ v.val :=
    le_trans p1_cut7_le_cut8 (le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10
      (le_trans p1_cut10_le_cut11 hv'.1)))
  have hge8 : p1_cut8 ≤ v.val :=
    le_trans p1_cut8_le_cut9 (le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1))
  have hge9 : p1_cut9 ≤ v.val := le_trans p1_cut9_le_cut10 (le_trans p1_cut10_le_cut11 hv'.1)
  have hge10 : p1_cut10 ≤ v.val := le_trans p1_cut10_le_cut11 hv'.1
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge hge1
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge hge2
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge hge3
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge hge4
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge hge5
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge hge6
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge hge7
  have hnot8 : ¬ v.val < p1_cut8 := by
    exact not_lt_of_ge hge8
  have hnot9 : ¬ v.val < p1_cut9 := by
    exact not_lt_of_ge hge9
  have hnot10 : ¬ v.val < p1_cut10 := by
    exact not_lt_of_ge hge10
  have hnot11 : ¬ v.val < p1_cut11 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hnot8, hnot9, hnot10, hnot11, hv'.2]

lemma ballotsAll_eq_ballot_adbec_of_mem_votersP1_13 {v : U311} (hv : v ∈ votersP1_13) :
    ballotsAll v = ballot_adbec := by
  have hv' := (mem_votersP1_13_iff v).1 hv
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut1 ≤ p1_cut12) hv'.1)
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut2 ≤ p1_cut12) hv'.1)
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut3 ≤ p1_cut12) hv'.1)
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut4 ≤ p1_cut12) hv'.1)
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut5 ≤ p1_cut12) hv'.1)
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut6 ≤ p1_cut12) hv'.1)
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut7 ≤ p1_cut12) hv'.1)
  have hnot8 : ¬ v.val < p1_cut8 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut8 ≤ p1_cut12) hv'.1)
  have hnot9 : ¬ v.val < p1_cut9 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut9 ≤ p1_cut12) hv'.1)
  have hnot10 : ¬ v.val < p1_cut10 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut10 ≤ p1_cut12) hv'.1)
  have hnot11 : ¬ v.val < p1_cut11 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut11 ≤ p1_cut12) hv'.1)
  have hnot12 : ¬ v.val < p1_cut12 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hnot8, hnot9, hnot10, hnot11, hnot12, hv'.2]

lemma ballotsAll_eq_ballot_bdeca_of_mem_votersP1_14 {v : U311} (hv : v ∈ votersP1_14) :
    ballotsAll v = ballot_bdeca := by
  have hv' := (mem_votersP1_14_iff v).1 hv
  have hnot1 : ¬ v.val < p1_cut1 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut1 ≤ p1_cut13) hv'.1)
  have hnot2 : ¬ v.val < p1_cut2 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut2 ≤ p1_cut13) hv'.1)
  have hnot3 : ¬ v.val < p1_cut3 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut3 ≤ p1_cut13) hv'.1)
  have hnot4 : ¬ v.val < p1_cut4 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut4 ≤ p1_cut13) hv'.1)
  have hnot5 : ¬ v.val < p1_cut5 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut5 ≤ p1_cut13) hv'.1)
  have hnot6 : ¬ v.val < p1_cut6 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut6 ≤ p1_cut13) hv'.1)
  have hnot7 : ¬ v.val < p1_cut7 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut7 ≤ p1_cut13) hv'.1)
  have hnot8 : ¬ v.val < p1_cut8 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut8 ≤ p1_cut13) hv'.1)
  have hnot9 : ¬ v.val < p1_cut9 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut9 ≤ p1_cut13) hv'.1)
  have hnot10 : ¬ v.val < p1_cut10 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut10 ≤ p1_cut13) hv'.1)
  have hnot11 : ¬ v.val < p1_cut11 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut11 ≤ p1_cut13) hv'.1)
  have hnot12 : ¬ v.val < p1_cut12 := by
    exact not_lt_of_ge (le_trans (by decide : p1_cut12 ≤ p1_cut13) hv'.1)
  have hnot13 : ¬ v.val < p1_cut13 := by
    exact not_lt_of_ge hv'.1
  simp [ballotsAll, ballotsAllCuts, ballotByCuts, hnot1, hnot2, hnot3, hnot4, hnot5, hnot6, hnot7, hnot8, hnot9, hnot10, hnot11, hnot12, hnot13]

noncomputable def FullProfile : Profile (Electorate U311 (Finset.univ)) A5 :=
  { pref := fun v => (ballotsAll v.1).toLinearOrder }

def votersP1 : Finset U311 :=
  Finset.univ.filter (fun v => v.val < p1_cut12)

lemma votersP1_eq_Ico : votersP1 = Finset.Ico 0 p1_cut12_fin := by
  ext v
  simp [votersP1, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut12_fin]

-- P2 obtained by block 12 joining P1
def votersP2 : Finset U311 :=
  Finset.univ.filter (fun v => v.val < p1_cut13)

lemma votersP2_eq_Ico : votersP2 = Finset.Ico 0 p1_cut13_fin := by
  ext v
  simp [votersP2, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut13_fin]

-- P3 obtained by block 11 leaving P2
def votersP3 : Finset U311 :=
  Finset.univ.filter (fun v => v.val < p1_cut10 ∨ (p1_cut11 ≤ v.val ∧ v.val < p1_cut13))

-- P4 obtained by block 14 joining P3
def votersP4 : Finset U311 :=
  Finset.univ.filter (fun v => v.val < p1_cut10 ∨ (p1_cut11 ≤ v.val ∧ v.val < p1_cut14))

-- P5 obtained by block 9 leaving P4
def votersP5 : Finset U311 :=
  Finset.univ.filter (fun v => v.val < p1_cut8 ∨ (p1_cut9 ≤ v.val ∧ v.val < p1_cut10) ∨
    (p1_cut11 ≤ v.val))

noncomputable def P1Profile : Profile (Electorate U311 votersP1) A5 :=
  restrictElectorate FullProfile votersP1 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P2Profile : Profile (Electorate U311 votersP2) A5 :=
  restrictElectorate FullProfile votersP2 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P3Profile : Profile (Electorate U311 votersP3) A5 :=
  restrictElectorate FullProfile votersP3 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P4Profile : Profile (Electorate U311 votersP4) A5 :=
  restrictElectorate FullProfile votersP4 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P5Profile : Profile (Electorate U311 votersP5) A5 :=
  restrictElectorate FullProfile votersP5 (by intro x hx ; exact Finset.mem_univ x)

lemma sum_Ico_split (a b c : U311) (f : U311 → Int) (hab : a ≤ b) (hbc : b ≤ c) :
    (Finset.Ico a c).sum f = (Finset.Ico a b).sum f + (Finset.Ico b c).sum f := by
  classical
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) :=
    Finset.Ico_disjoint_Ico_consecutive a b c
  have hunion : Finset.Ico a b ∪ Finset.Ico b c = Finset.Ico a c :=
    Finset.Ico_union_Ico_eq_Ico hab hbc
  calc
    (Finset.Ico a c).sum f =
        ((Finset.Ico a b ∪ Finset.Ico b c).sum f) := by simp [hunion]
    _ = (Finset.Ico a b).sum f + (Finset.Ico b c).sum f := by
        exact Finset.sum_union hdisj

def p1_cut_list : List U311 :=
  [0, p1_cut1_fin, p1_cut2_fin, p1_cut3_fin, p1_cut4_fin, p1_cut5_fin, p1_cut6_fin,
   p1_cut7_fin, p1_cut8_fin, p1_cut9_fin, p1_cut10_fin, p1_cut11_fin, p1_cut12_fin]

def lastOf (a : U311) : List U311 → U311
  | [] => a
  | b :: rest => lastOf b rest

def sum_Ico_chain (a : U311) : List U311 → (U311 → Int) → Int
  | [], _ => 0
  | b :: rest, f => (Finset.Ico a b).sum f + sum_Ico_chain b rest f

lemma le_lastOf_of_chain {a : U311} {rest : List U311} :
    List.IsChain (· ≤ ·) (a :: rest) → a ≤ lastOf a rest := by
  intro hchain
  cases rest with
  | nil =>
      simp [lastOf]
  | cons b rest =>
      have hchain' := (List.isChain_cons_cons).1 hchain
      have hab : a ≤ b := hchain'.1
      have hchain_tail : List.IsChain (· ≤ ·) (b :: rest) := hchain'.2
      have hbc : b ≤ lastOf b rest := le_lastOf_of_chain hchain_tail
      exact le_trans hab hbc

lemma sum_Ico_chain_eq (a : U311) (rest : List U311) (f : U311 → Int)
    (hchain : List.IsChain (· ≤ ·) (a :: rest)) :
    sum_Ico_chain a rest f = (Finset.Ico a (lastOf a rest)).sum f := by
  cases rest with
  | nil =>
      simp [sum_Ico_chain, lastOf]
  | cons b rest =>
      have hchain' := (List.isChain_cons_cons).1 hchain
      have hab : a ≤ b := hchain'.1
      have hchain_tail : List.IsChain (· ≤ ·) (b :: rest) := hchain'.2
      have hbc : b ≤ lastOf b rest := le_lastOf_of_chain hchain_tail
      have ih := sum_Ico_chain_eq (a := b) (rest := rest) (f := f) hchain_tail
      calc
        sum_Ico_chain a (b :: rest) f =
            (Finset.Ico a b).sum f + sum_Ico_chain b rest f := by
              simp [sum_Ico_chain]
        _ = (Finset.Ico a b).sum f + (Finset.Ico b (lastOf b rest)).sum f := by
              simp [ih]
        _ = (Finset.Ico a (lastOf b rest)).sum f := by
              symm
              exact sum_Ico_split (a := a) (b := b) (c := lastOf b rest) f hab hbc
        _ = (Finset.Ico a (lastOf a (b :: rest))).sum f := by
              simp [lastOf]

lemma sum_Ico_chain_p1 (f : U311 → Int) :
    (Finset.Ico (0 : U311) p1_cut12_fin).sum f =
      sum_Ico_chain 0 p1_cut_list.tail f := by
  have hchain : List.IsChain (· ≤ ·) p1_cut_list := by decide
  have hsum :=
    sum_Ico_chain_eq (a := 0) (rest := p1_cut_list.tail) (f := f)
      (by simpa [p1_cut_list] using hchain)
  simpa [p1_cut_list, lastOf] using hsum.symm

lemma sum_Ico_chain_p1_13 (f : U311 → Int) :
    (Finset.Ico (0 : U311) p1_cut13_fin).sum f =
      sum_Ico_chain 0 [p1_cut12_fin, p1_cut13_fin] f := by
  have hchain : List.IsChain (· ≤ ·) ([0, p1_cut12_fin, p1_cut13_fin] : List U311) := by
    decide
  have hsum :=
    sum_Ico_chain_eq (a := 0) (rest := [p1_cut12_fin, p1_cut13_fin]) (f := f)
      (by simpa using hchain)
  simpa [lastOf] using hsum.symm

lemma sum_marginOfBallot_const (S : Finset U311) (ballot : ListBallot 5) (a b : A5)
    (hconst : ∀ v, v ∈ S → ballotsAll v = ballot) :
    S.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (S.card : Int) * marginOfBallot ballot a b := by
  classical
  have hsum :
      S.sum (fun v => marginOfBallot (ballotsAll v) a b) =
        S.card • marginOfBallot ballot a b := by
    refine Finset.sum_eq_card_nsmul ?_
    intro v hv
    simp [hconst v hv]
  simpa [Int.nsmul_eq_mul] using hsum

lemma prefers_restrictElectorate_iff_prefersInList (S : Finset U311)
    (v : Electorate U311 S) (a b : A5) :
    Prefers (restrictElectorate FullProfile S (by intro x _; exact Finset.mem_univ x)) v a b ↔
      prefersInList (ballotsAll v.1).ranking a b = true := by
  unfold Prefers restrictElectorate FullProfile prefersInList
  simp only
  rw [ListBallot.lt_iff_idxOf]
  simp [decide_eq_true_eq]

lemma margin_restrictElectorate_eq_sum_marginOfBallot (S : Finset U311) {a b : A5} (hne : a ≠ b) :
    margin (restrictElectorate FullProfile S (by intro x _; exact Finset.mem_univ x)) a b =
      S.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
  classical
  set P := restrictElectorate FullProfile S (by intro x _; exact Finset.mem_univ x) with hP
  have hpref :
      ∀ v : Electorate U311 S,
        Prefers P v a b ↔ prefersInList (ballotsAll v.1).ranking a b = true := by
    intro v
    simpa [hP] using
      (prefers_restrictElectorate_iff_prefersInList (S := S) (v := v) (a := a) (b := b))
  have hpref_ba :
      ∀ v : Electorate U311 S,
        Prefers P v b a ↔ prefersInList (ballotsAll v.1).ranking b a = true := by
    intro v
    simpa [hP] using
      (prefers_restrictElectorate_iff_prefersInList (S := S) (v := v) (a := b) (b := a))
  have hcount_ab :
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S => Prefers P v a b)).card) =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) := by
    calc
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S => Prefers P v a b)).card) =
          (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S =>
            prefersInList (ballotsAll v.1).ranking a b = true)).card) := by
            simp [hpref]
      _ = (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
            if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) := by
            simp
  have hcount_ba :
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S => Prefers P v b a)).card) =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) := by
    calc
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S => Prefers P v b a)).card) =
          (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S =>
            prefersInList (ballotsAll v.1).ranking b a = true)).card) := by
            simp [hpref_ba]
      _ = (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
            if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) := by
            simp
  have hsum :
      (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          (if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
            (if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0)) := by
    symm
    exact Finset.sum_sub_distrib _ _
  have hsum' :
      (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          (if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
            (if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0)) =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := by
    refine Finset.sum_congr rfl ?_
    intro v _hv
    simp [marginOfBallot_eq_sub_indicators (b := ballotsAll v.1) (hne := hne)]
  have hmargin :
      margin P a b =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := by
    calc
      margin P a b =
          (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S => Prefers P v a b)).card) -
            (Int.ofNat (Finset.univ.filter (fun v : Electorate U311 S => Prefers P v b a)).card) := by
          simp [margin, hP]
      _ =
          (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
              if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
            (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
              if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) := by
          rw [hcount_ab, hcount_ba]
      _ =
          (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
            (if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
              (if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0)) := hsum
      _ = (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
            marginOfBallot (ballotsAll v.1) a b) := hsum'
  have hsum_subtype :
      S.sum (fun v => marginOfBallot (ballotsAll v) a b) =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := by
    refine (Finset.sum_subtype (s := S) (p := fun v => v ∈ S) ?_
      (f := fun v => marginOfBallot (ballotsAll v) a b))
    intro x
    simp
  calc
    margin P a b =
        (Finset.univ : Finset (Electorate U311 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := hmargin
    _ = S.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
        symm
        simp [hsum_subtype]

lemma sum_votersP1_1_marginOfBallot (a b : A5) :
    votersP1_1.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (63 : Int) * marginOfBallot ballot_acdeb a b := by
  simpa [card_votersP1_1] using
    (sum_marginOfBallot_const (S := votersP1_1) (ballot := ballot_acdeb) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_acdeb_of_mem_votersP1_1 hv))

lemma sum_votersP1_2_marginOfBallot (a b : A5) :
    votersP1_2.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (39 : Int) * marginOfBallot ballot_baced a b := by
  simpa [card_votersP1_2] using
    (sum_marginOfBallot_const (S := votersP1_2) (ballot := ballot_baced) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_baced_of_mem_votersP1_2 hv))

lemma sum_votersP1_3_marginOfBallot (a b : A5) :
    votersP1_3.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (35 : Int) * marginOfBallot ballot_ebdca a b := by
  simpa [card_votersP1_3] using
    (sum_marginOfBallot_const (S := votersP1_3) (ballot := ballot_ebdca) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_ebdca_of_mem_votersP1_3 hv))

lemma sum_votersP1_4_marginOfBallot (a b : A5) :
    votersP1_4.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (24 : Int) * marginOfBallot ballot_bacde a b := by
  simpa [card_votersP1_4] using
    (sum_marginOfBallot_const (S := votersP1_4) (ballot := ballot_bacde) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_bacde_of_mem_votersP1_4 hv))

lemma sum_votersP1_5_marginOfBallot (a b : A5) :
    votersP1_5.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (21 : Int) * marginOfBallot ballot_cebda a b := by
  simpa [card_votersP1_5] using
    (sum_marginOfBallot_const (S := votersP1_5) (ballot := ballot_cebda) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_cebda_of_mem_votersP1_5 hv))

lemma sum_votersP1_6_marginOfBallot (a b : A5) :
    votersP1_6.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (22 : Int) * marginOfBallot ballot_edbac a b := by
  simpa [card_votersP1_6] using
    (sum_marginOfBallot_const (S := votersP1_6) (ballot := ballot_edbac) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_edbac_of_mem_votersP1_6 hv))

lemma sum_votersP1_7_marginOfBallot (a b : A5) :
    votersP1_7.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (11 : Int) * marginOfBallot ballot_edcba a b := by
  simpa [card_votersP1_7] using
    (sum_marginOfBallot_const (S := votersP1_7) (ballot := ballot_edcba) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_edcba_of_mem_votersP1_7 hv))

lemma sum_votersP1_8_marginOfBallot (a b : A5) :
    votersP1_8.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (10 : Int) * marginOfBallot ballot_dacbe a b := by
  simpa [card_votersP1_8] using
    (sum_marginOfBallot_const (S := votersP1_8) (ballot := ballot_dacbe) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_dacbe_of_mem_votersP1_8 hv))

lemma sum_votersP1_9_marginOfBallot (a b : A5) :
    votersP1_9.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (14 : Int) * marginOfBallot ballot_dceba a b := by
  simpa [card_votersP1_9] using
    (sum_marginOfBallot_const (S := votersP1_9) (ballot := ballot_dceba) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_dceba_of_mem_votersP1_9 hv))

lemma sum_votersP1_10_marginOfBallot (a b : A5) :
    votersP1_10.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (8 : Int) * marginOfBallot ballot_daecb a b := by
  simpa [card_votersP1_10] using
    (sum_marginOfBallot_const (S := votersP1_10) (ballot := ballot_daecb) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_daecb_of_mem_votersP1_10 hv))

lemma sum_votersP1_11_marginOfBallot (a b : A5) :
    votersP1_11.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (6 : Int) * marginOfBallot ballot_bdace a b := by
  simpa [card_votersP1_11] using
    (sum_marginOfBallot_const (S := votersP1_11) (ballot := ballot_bdace) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_bdace_of_mem_votersP1_11 hv))

lemma sum_votersP1_12_marginOfBallot (a b : A5) :
    votersP1_12.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (4 : Int) * marginOfBallot ballot_aecbd a b := by
  simpa [card_votersP1_12] using
    (sum_marginOfBallot_const (S := votersP1_12) (ballot := ballot_aecbd) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_aecbd_of_mem_votersP1_12 hv))

lemma sum_votersP1_13_marginOfBallot (a b : A5) :
    votersP1_13.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (28 : Int) * marginOfBallot ballot_adbec a b := by
  simpa [card_votersP1_13] using
    (sum_marginOfBallot_const (S := votersP1_13) (ballot := ballot_adbec) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_adbec_of_mem_votersP1_13 hv))

lemma sum_votersP1_14_marginOfBallot (a b : A5) :
    votersP1_14.sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (26 : Int) * marginOfBallot ballot_bdeca a b := by
  simpa [card_votersP1_14] using
    (sum_marginOfBallot_const (S := votersP1_14) (ballot := ballot_bdeca) (a := a) (b := b)
      (by intro v hv; exact ballotsAll_eq_ballot_bdeca_of_mem_votersP1_14 hv))

lemma votersP1_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP1.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP1 a b := by
  classical
  let f : U311 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum :
      votersP1.sum f =
        (63 : Int) * marginOfBallot ballot_acdeb a b +
        (39 : Int) * marginOfBallot ballot_baced a b +
        (35 : Int) * marginOfBallot ballot_ebdca a b +
        (24 : Int) * marginOfBallot ballot_bacde a b +
        (21 : Int) * marginOfBallot ballot_cebda a b +
        (22 : Int) * marginOfBallot ballot_edbac a b +
        (11 : Int) * marginOfBallot ballot_edcba a b +
        (10 : Int) * marginOfBallot ballot_dacbe a b +
        (14 : Int) * marginOfBallot ballot_dceba a b +
        (8 : Int) * marginOfBallot ballot_daecb a b +
        (6 : Int) * marginOfBallot ballot_bdace a b +
        (4 : Int) * marginOfBallot ballot_aecbd a b := by
    simp [f, votersP1_eq_Ico, sum_Ico_chain_p1, p1_cut_list, sum_Ico_chain,
      ← votersP1_1_eq_Ico, ← votersP1_2_eq_Ico, ← votersP1_3_eq_Ico, ← votersP1_4_eq_Ico,
      ← votersP1_5_eq_Ico, ← votersP1_6_eq_Ico, ← votersP1_7_eq_Ico, ← votersP1_8_eq_Ico,
      ← votersP1_9_eq_Ico, ← votersP1_10_eq_Ico, ← votersP1_11_eq_Ico, ← votersP1_12_eq_Ico,
      sum_votersP1_1_marginOfBallot, sum_votersP1_2_marginOfBallot, sum_votersP1_3_marginOfBallot,
      sum_votersP1_4_marginOfBallot, sum_votersP1_5_marginOfBallot, sum_votersP1_6_marginOfBallot,
      sum_votersP1_7_marginOfBallot, sum_votersP1_8_marginOfBallot, sum_votersP1_9_marginOfBallot,
      sum_votersP1_10_marginOfBallot, sum_votersP1_11_marginOfBallot,
      sum_votersP1_12_marginOfBallot, add_assoc]
  calc
    votersP1.sum f =
        (63 : Int) * marginOfBallot ballot_acdeb a b +
        (39 : Int) * marginOfBallot ballot_baced a b +
        (35 : Int) * marginOfBallot ballot_ebdca a b +
        (24 : Int) * marginOfBallot ballot_bacde a b +
        (21 : Int) * marginOfBallot ballot_cebda a b +
        (22 : Int) * marginOfBallot ballot_edbac a b +
        (11 : Int) * marginOfBallot ballot_edcba a b +
        (10 : Int) * marginOfBallot ballot_dacbe a b +
        (14 : Int) * marginOfBallot ballot_dceba a b +
        (8 : Int) * marginOfBallot ballot_daecb a b +
        (6 : Int) * marginOfBallot ballot_bdace a b +
        (4 : Int) * marginOfBallot ballot_aecbd a b := hsum
    _ = marginBlocks blocksP1 a b := by
      simp [marginBlocks, blocksP1]

lemma votersP2_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP2.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP2 a b := by
  classical
  let f : U311 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum : votersP2.sum f = votersP1.sum f + votersP1_13.sum f := by
    simp [votersP2_eq_Ico, votersP1_eq_Ico, votersP1_13_eq_Ico, sum_Ico_chain_p1_13,
      sum_Ico_chain]
  calc
    votersP2.sum f = votersP1.sum f + votersP1_13.sum f := hsum
    _ = marginBlocks blocksP2 a b := by
      simp [f, votersP1_sum_marginOfBallot_eq_marginBlocks, sum_votersP1_13_marginOfBallot,
        marginBlocks, blocksP2, blocksP1]

lemma votersP1_11_subset_votersP2 : votersP1_11 ⊆ votersP2 := by
  intro v hv
  have hv' := (mem_votersP1_11_iff v).1 hv
  have hlt13 : v.val < p1_cut13 := lt_of_lt_of_le hv'.2 (by decide : p1_cut11 ≤ p1_cut13)
  simp [votersP2, hlt13]

lemma votersP4_eq_union_sdiff : votersP4 = (votersP2 \ votersP1_11) ∪ votersP1_14 := by
  ext v
  constructor
  · intro hv
    have hv' :
        v.val < p1_cut10 ∨ (p1_cut11 ≤ v.val ∧ v.val < p1_cut14) := by
      simpa [votersP4] using (Finset.mem_filter.mp hv).2
    cases hv' with
    | inl hlt10 =>
        have hlt13 : v.val < p1_cut13 := lt_of_lt_of_le hlt10 (by decide : p1_cut10 ≤ p1_cut13)
        have hv2 : v ∈ votersP2 := by
          simp [votersP2, hlt13]
        have hv11 : v ∉ votersP1_11 := by
          intro hv11
          have hv11' := (mem_votersP1_11_iff v).1 hv11
          exact (not_lt_of_ge hv11'.1) hlt10
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hv2, hv11⟩))
    | inr hge11 =>
        by_cases hlt13 : v.val < p1_cut13
        · have hv2 : v ∈ votersP2 := by
            simp [votersP2, hlt13]
          have hv11 : v ∉ votersP1_11 := by
            intro hv11
            have hv11' := (mem_votersP1_11_iff v).1 hv11
            exact (not_lt_of_ge hge11.1) hv11'.2
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hv2, hv11⟩))
        · have hge13 : p1_cut13 ≤ v.val := le_of_not_gt hlt13
          have hv14 : v ∈ votersP1_14 := by
            exact (mem_votersP1_14_iff v).2 ⟨hge13, hge11.2⟩
          exact Finset.mem_union.mpr (Or.inr hv14)
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_sdiff.mp hv with ⟨hv2, hv11⟩
      have hv2' : v.val < p1_cut13 := by
        simpa [votersP2] using (Finset.mem_filter.mp hv2).2
      by_cases hlt10 : v.val < p1_cut10
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hlt10⟩)
      · have hge10 : p1_cut10 ≤ v.val := le_of_not_gt hlt10
        have hnot11 : ¬ v.val < p1_cut11 := by
          intro hlt11
          exact hv11 ((mem_votersP1_11_iff v).2 ⟨hge10, hlt11⟩)
        have hge11 : p1_cut11 ≤ v.val := le_of_not_gt hnot11
        exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hge11, v.2⟩⟩)
    · have hv14' := (mem_votersP1_14_iff v).1 hv
      have hge11 : p1_cut11 ≤ v.val := by
        exact le_trans (by decide : p1_cut11 ≤ p1_cut13) hv14'.1
      exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hge11, hv14'.2⟩⟩)

lemma votersP4_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP4.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP4 a b := by
  classical
  let f : U311 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum_sdiff :
      (votersP2 \ votersP1_11).sum f = votersP2.sum f - votersP1_11.sum f := by
    simpa using
      (Finset.sum_sdiff_eq_sub (s₁ := votersP1_11) (s₂ := votersP2) (f := f)
        votersP1_11_subset_votersP2)
  have hdisj : Disjoint (votersP2 \ votersP1_11) votersP1_14 := by
    refine Finset.disjoint_left.2 ?_
    intro v hv2 hv14
    have hv2' : v.val < p1_cut13 := by
      simpa [votersP2] using (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv2).1).2
    have hv14' := (mem_votersP1_14_iff v).1 hv14
    exact (not_lt_of_ge hv14'.1) hv2'
  have hsum_union :
      votersP4.sum f = (votersP2 \ votersP1_11).sum f + votersP1_14.sum f := by
    simpa [votersP4_eq_union_sdiff] using
      (Finset.sum_union (s₁ := votersP2 \ votersP1_11) (s₂ := votersP1_14) (f := f) hdisj)
  calc
    votersP4.sum f = (votersP2 \ votersP1_11).sum f + votersP1_14.sum f := hsum_union
    _ = (votersP2.sum f - votersP1_11.sum f) + votersP1_14.sum f := by
        simp [hsum_sdiff]
    _ = marginBlocks blocksP4 a b := by
        simp [f, votersP2_sum_marginOfBallot_eq_marginBlocks, sum_votersP1_11_marginOfBallot,
          sum_votersP1_14_marginOfBallot, marginBlocks, blocksP4, blocksP3, blocksP2, blocksP1]
        ring

lemma margin_P1Profile_eq_blocks {a b : A5} (hne : a ≠ b) :
    margin P1Profile a b = marginBlocks blocksP1 a b := by
  calc
    margin P1Profile a b =
        votersP1.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
      simpa [P1Profile] using
        (margin_restrictElectorate_eq_sum_marginOfBallot (S := votersP1) (a := a) (b := b) (hne := hne))
    _ = marginBlocks blocksP1 a b := votersP1_sum_marginOfBallot_eq_marginBlocks (a := a) (b := b)

lemma margin_P2Profile_eq_blocks {a b : A5} (hne : a ≠ b) :
    margin P2Profile a b = marginBlocks blocksP2 a b := by
  calc
    margin P2Profile a b =
        votersP2.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
      simpa [P2Profile] using
        (margin_restrictElectorate_eq_sum_marginOfBallot (S := votersP2) (a := a) (b := b) (hne := hne))
    _ = marginBlocks blocksP2 a b := votersP2_sum_marginOfBallot_eq_marginBlocks (a := a) (b := b)

lemma margin_P4Profile_eq_blocks {a b : A5} (hne : a ≠ b) :
    margin P4Profile a b = marginBlocks blocksP4 a b := by
  calc
    margin P4Profile a b =
        votersP4.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
      simpa [P4Profile] using
        (margin_restrictElectorate_eq_sum_marginOfBallot (S := votersP4) (a := a) (b := b) (hne := hne))
    _ = marginBlocks blocksP4 a b := votersP4_sum_marginOfBallot_eq_marginBlocks (a := a) (b := b)

lemma marginBlocks_P1_b_a : marginBlocks blocksP1 b a = 87 := by
  decide

lemma marginBlocks_P2_b_a : marginBlocks blocksP2 b a = 59 := by
  decide

lemma marginBlocks_P4_b_a : marginBlocks blocksP4 b a = 79 := by
  decide

lemma margin_P1Profile_b_a : margin P1Profile b a = 87 := by
  calc
    margin P1Profile b a = marginBlocks blocksP1 b a := margin_P1Profile_eq_blocks (a := b) (b := a)
      (by decide)
    _ = 87 := by simpa using marginBlocks_P1_b_a

lemma margin_P2Profile_b_a : margin P2Profile b a = 59 := by
  calc
    margin P2Profile b a = marginBlocks blocksP2 b a := margin_P2Profile_eq_blocks (a := b) (b := a)
      (by decide)
    _ = 59 := by simpa using marginBlocks_P2_b_a

lemma margin_P4Profile_b_a : margin P4Profile b a = 79 := by
  calc
    margin P4Profile b a = marginBlocks blocksP4 b a := margin_P4Profile_eq_blocks (a := b) (b := a)
      (by decide)
    _ = 79 := by simpa using marginBlocks_P4_b_a

end Holliday

end SocialChoice
