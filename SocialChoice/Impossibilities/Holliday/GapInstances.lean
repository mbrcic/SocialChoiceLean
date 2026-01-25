import Mathlib.Tactic
import SocialChoice.Impossibilities.Holliday.GapWitnesses
import SocialChoice.Impossibilities.Holliday.MarginDifferences
import SocialChoice.Impossibilities.Holliday.Margins

namespace SocialChoice

namespace Holliday

attribute [simp]
  margin_P1Profile_a_b margin_P1Profile_a_c margin_P1Profile_a_d margin_P1Profile_a_e
  margin_P1Profile_b_a margin_P1Profile_b_c margin_P1Profile_b_d margin_P1Profile_b_e
  margin_P1Profile_c_d margin_P1Profile_c_e margin_P1Profile_d_e
  margin_P3Profile_a_b margin_P3Profile_a_c margin_P3Profile_a_d margin_P3Profile_a_e
  margin_P3Profile_b_c margin_P3Profile_b_d margin_P3Profile_b_e margin_P3Profile_c_d
  margin_P3Profile_c_e margin_P3Profile_d_e
  margin_P5Profile_a_b margin_P5Profile_a_c margin_P5Profile_a_d margin_P5Profile_a_e
  margin_P5Profile_b_c margin_P5Profile_b_d margin_P5Profile_b_e margin_P5Profile_c_d
  margin_P5Profile_c_e margin_P5Profile_d_e

@[simp] lemma margin_P1Profile_c_a : margin P1Profile c a = (-83 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) a c
  simp [margin_P1Profile_a_c] at h
  linarith

@[simp] lemma margin_P1Profile_d_a : margin P1Profile d a = (-1 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) a d
  simp [margin_P1Profile_a_d] at h
  linarith

@[simp] lemma margin_P1Profile_e_a : margin P1Profile e a = (-47 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) a e
  simp [margin_P1Profile_a_e] at h
  linarith

@[simp] lemma margin_P1Profile_c_b : margin P1Profile c b = (-37 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) b c
  simp [margin_P1Profile_b_c] at h
  linarith

@[simp] lemma margin_P1Profile_d_b : margin P1Profile d b = (-1 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) b d
  simp [margin_P1Profile_b_d] at h
  linarith

@[simp] lemma margin_P1Profile_e_b : margin P1Profile e b = (91 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) b e
  simp [margin_P1Profile_b_e] at h
  linarith

@[simp] lemma margin_P1Profile_d_c : margin P1Profile d c = (-41 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) c d
  simp [margin_P1Profile_c_d] at h
  linarith

@[simp] lemma margin_P1Profile_e_c : margin P1Profile e c = (-87 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) c e
  simp [margin_P1Profile_c_e] at h
  linarith

@[simp] lemma margin_P1Profile_e_d : margin P1Profile e d = (5 : Int) := by
  have h := margin_antisymmetric (P := P1Profile) d e
  simp [margin_P1Profile_d_e] at h
  linarith

lemma exists_pos_margin_into_P1 (y : A5) : ∃ z, 0 < margin P1Profile z y := by
  fin_cases y
  · refine ⟨b, ?_⟩
    simp
  · refine ⟨e, ?_⟩
    simp
  · refine ⟨a, ?_⟩
    simp
  · refine ⟨c, ?_⟩
    simp
  · refine ⟨c, ?_⟩
    simp

@[simp] lemma margin_P3Profile_b_a : margin P3Profile b a = (62 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) a b
  simp [margin_P3Profile_a_b] at h
  linarith

@[simp] lemma margin_P3Profile_c_a : margin P3Profile c a = (-102 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) a c
  simp [margin_P3Profile_a_c] at h
  linarith

@[simp] lemma margin_P3Profile_d_a : margin P3Profile d a = (-34 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) a d
  simp [margin_P3Profile_a_d] at h
  linarith

@[simp] lemma margin_P3Profile_e_a : margin P3Profile e a = (-66 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) a e
  simp [margin_P3Profile_a_e] at h
  linarith

@[simp] lemma margin_P3Profile_c_b : margin P3Profile c b = (-70 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) b c
  simp [margin_P3Profile_b_c] at h
  linarith

@[simp] lemma margin_P3Profile_d_b : margin P3Profile d b = (18 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) b d
  simp [margin_P3Profile_b_d] at h
  linarith

@[simp] lemma margin_P3Profile_e_b : margin P3Profile e b = (58 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) b e
  simp [margin_P3Profile_b_e] at h
  linarith

@[simp] lemma margin_P3Profile_d_c : margin P3Profile d c = (-22 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) c d
  simp [margin_P3Profile_c_d] at h
  linarith

@[simp] lemma margin_P3Profile_e_c : margin P3Profile e c = (-54 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) c e
  simp [margin_P3Profile_c_e] at h
  linarith

@[simp] lemma margin_P3Profile_e_d : margin P3Profile e d = (-14 : Int) := by
  have h := margin_antisymmetric (P := P3Profile) d e
  simp [margin_P3Profile_d_e] at h
  linarith

@[simp] lemma margin_P5Profile_b_a : margin P5Profile b a = (78 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) a b
  simp [margin_P5Profile_a_b] at h
  linarith

@[simp] lemma margin_P5Profile_c_a : margin P5Profile c a = (-118 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) a c
  simp [margin_P5Profile_a_c] at h
  linarith

@[simp] lemma margin_P5Profile_d_a : margin P5Profile d a = (-18 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) a d
  simp [margin_P5Profile_a_d] at h
  linarith

@[simp] lemma margin_P5Profile_e_a : margin P5Profile e a = (-36 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) a e
  simp [margin_P5Profile_a_e] at h
  linarith

@[simp] lemma margin_P5Profile_c_b : margin P5Profile c b = (-86 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) b c
  simp [margin_P5Profile_b_c] at h
  linarith

@[simp] lemma margin_P5Profile_d_b : margin P5Profile d b = (-12 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) b d
  simp [margin_P5Profile_b_d] at h
  linarith

@[simp] lemma margin_P5Profile_e_b : margin P5Profile e b = (42 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) b e
  simp [margin_P5Profile_b_e] at h
  linarith

@[simp] lemma margin_P5Profile_d_c : margin P5Profile d c = (-6 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) c d
  simp [margin_P5Profile_c_d] at h
  linarith

@[simp] lemma margin_P5Profile_e_c : margin P5Profile e c = (-24 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) c e
  simp [margin_P5Profile_c_e] at h
  linarith

@[simp] lemma margin_P5Profile_e_d : margin P5Profile e d = (-30 : Int) := by
  have h := margin_antisymmetric (P := P5Profile) d e
  simp [margin_P5Profile_d_e] at h
  linarith

lemma edgeWeights_P1_le_91 {m : Int} (hm : m ∈ edgeWeights_P1) : m ≤ (91 : Int) := by
  have hm' :
      m = 81 ∨ m = 83 ∨ m = 1 ∨ m = 47 ∨ m = 37 ∨ m = 91 ∨ m = 41 ∨ m = 87 ∨ m = 5 := by
    simpa [edgeWeights_P1] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P1_ge_1 {m : Int} (hm : m ∈ edgeWeights_P1) : (1 : Int) ≤ m := by
  have hm' :
      m = 81 ∨ m = 83 ∨ m = 1 ∨ m = 47 ∨ m = 37 ∨ m = 91 ∨ m = 41 ∨ m = 87 ∨ m = 5 := by
    simpa [edgeWeights_P1] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P3_le_170 {m : Int} (hm : m ∈ edgeWeights_P3) : m ≤ (170 : Int) := by
  have hm' :
      m = 62 ∨ m = 102 ∨ m = 34 ∨ m = 66 ∨ m = 70 ∨ m = 18 ∨ m = 58 ∨
        m = 22 ∨ m = 54 ∨ m = 14 := by
    simpa [edgeWeights_P3] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P3_le_102 {m : Int} (hm : m ∈ edgeWeights_P3) : m ≤ (102 : Int) := by
  have hm' :
      m = 62 ∨ m = 102 ∨ m = 34 ∨ m = 66 ∨ m = 70 ∨ m = 18 ∨ m = 58 ∨
        m = 22 ∨ m = 54 ∨ m = 14 := by
    simpa [edgeWeights_P3] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P5_le_170 {m : Int} (hm : m ∈ edgeWeights_P5) : m ≤ (170 : Int) := by
  have hm' :
      m = 78 ∨ m = 118 ∨ m = 18 ∨ m = 36 ∨ m = 86 ∨ m = 12 ∨ m = 42 ∨
        m = 6 ∨ m = 24 ∨ m = 30 := by
    simpa [edgeWeights_P5] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P5_le_118 {m : Int} (hm : m ∈ edgeWeights_P5) : m ≤ (118 : Int) := by
  have hm' :
      m = 78 ∨ m = 118 ∨ m = 18 ∨ m = 36 ∨ m = 86 ∨ m = 12 ∨ m = 42 ∨
        m = 6 ∨ m = 24 ∨ m = 30 := by
    simpa [edgeWeights_P5] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P3_ge_6 {m : Int} (hm : m ∈ edgeWeights_P3) : (6 : Int) ≤ m := by
  have hm' :
      m = 62 ∨ m = 102 ∨ m = 34 ∨ m = 66 ∨ m = 70 ∨ m = 18 ∨ m = 58 ∨
        m = 22 ∨ m = 54 ∨ m = 14 := by
    simpa [edgeWeights_P3] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma edgeWeights_P5_ge_6 {m : Int} (hm : m ∈ edgeWeights_P5) : (6 : Int) ≤ m := by
  have hm' :
      m = 78 ∨ m = 118 ∨ m = 18 ∨ m = 36 ∨ m = 86 ∨ m = 12 ∨ m = 42 ∨
        m = 6 ∨ m = 24 ∨ m = 30 := by
    simpa [edgeWeights_P5] using hm
  rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma margin_P1Profile_pos_mem_edgeWeights {x y : A5}
    (hpos : 0 < margin P1Profile x y) : margin P1Profile x y ∈ edgeWeights_P1 := by
  fin_cases x <;> fin_cases y <;>
    simp [edgeWeights_P1, self_margin_zero] at hpos ⊢

lemma margin_P3Profile_pos_mem_edgeWeights {x y : A5}
    (hpos : 0 < margin P3Profile x y) : margin P3Profile x y ∈ edgeWeights_P3 := by
  fin_cases x <;> fin_cases y <;>
    simp [edgeWeights_P3, self_margin_zero] at hpos ⊢

lemma margin_P5Profile_pos_mem_edgeWeights {x y : A5}
    (hpos : 0 < margin P5Profile x y) : margin P5Profile x y ∈ edgeWeights_P5 := by
  fin_cases x <;> fin_cases y <;>
    simp [edgeWeights_P5, self_margin_zero] at hpos ⊢

lemma margin_P1Profile_ne_zero_of_ne {x y : A5} (hxy : x ≠ y) :
    margin P1Profile x y ≠ 0 := by
  fin_cases x <;> fin_cases y <;>
    simp at hxy ⊢

lemma margin_P3Profile_ne_zero_of_ne {x y : A5} (hxy : x ≠ y) :
    margin P3Profile x y ≠ 0 := by
  fin_cases x <;> fin_cases y <;>
    simp at hxy ⊢

lemma margin_P5Profile_ne_zero_of_ne {x y : A5} (hxy : x ≠ y) :
    margin P5Profile x y ≠ 0 := by
  fin_cases x <;> fin_cases y <;>
    simp at hxy ⊢

lemma margin_P3Profile_pos_ne_pos {x y z : A5}
    (hpos1 : 0 < margin P3Profile y x) (hpos2 : 0 < margin P3Profile z y) :
    margin P3Profile y x ≠ margin P3Profile z y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [self_margin_zero] at hpos1 hpos2 ⊢

lemma margin_P5Profile_pos_ne_pos {x y z : A5}
    (hpos1 : 0 < margin P5Profile y x) (hpos2 : 0 < margin P5Profile z y) :
    margin P5Profile y x ≠ margin P5Profile z y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp [self_margin_zero] at hpos1 hpos2 ⊢

lemma hgap_P1Profile {x y : A5}
    (hy : ∀ z, margin P1Profile z y < margin P1Profile y x) :
    ∃ W : Finset U450, Disjoint votersP1 W ∧
      (W.card : Int) < margin P1Profile y x ∧
      (∀ z, margin P1Profile z y < (W.card : Int)) := by
  classical
  have hmpos : 0 < margin P1Profile y x := by
    simpa [self_margin_zero] using (hy y)
  have hm_mem : margin P1Profile y x ∈ edgeWeights_P1 :=
    margin_P1Profile_pos_mem_edgeWeights (x := y) (y := x) hmpos
  have hm_ge2 : (2 : Int) ≤ margin P1Profile y x := by
    obtain ⟨z, hz⟩ := exists_pos_margin_into_P1 y
    have hlt : margin P1Profile z y < margin P1Profile y x := hy z
    linarith [hz, hlt]
  set k : Int := margin P1Profile y x - 1 with hk
  have hk0 : 0 ≤ k := by
    linarith [hm_ge2]
  have hk_le : k ≤ (170 : Int) := by
    have hm_le : margin P1Profile y x ≤ (91 : Int) := edgeWeights_P1_le_91 hm_mem
    linarith
  have hk_nat : k.toNat ≤ 170 := (Int.toNat_le (m := k) (n := 170)).2 hk_le
  obtain ⟨W, hdisj, hcard⟩ :=
    exists_disjoint_W_of_int_card_le_170 (V := votersP1)
      votersP1_subset_Iio_u280 hk0 hk_nat
  refine ⟨W, hdisj, ?_, ?_⟩
  · have hklt : k < margin P1Profile y x := by
      linarith
    simp [hcard, hk]
  · intro z
    by_cases hzpos : 0 < margin P1Profile z y
    · have hz_mem : margin P1Profile z y ∈ edgeWeights_P1 :=
        margin_P1Profile_pos_mem_edgeWeights (x := z) (y := y) hzpos
      have hne' : margin P1Profile z y ≠ margin P1Profile y x := by
        exact ne_of_lt (hy z)
      have hne : margin P1Profile y x ≠ margin P1Profile z y := by
        exact ne_comm.mp hne'
      have hgap_nat :
          2 ≤ Int.natAbs (margin P1Profile y x - margin P1Profile z y) :=
        edgeWeights_P1_gap2 _ hm_mem _ hz_mem hne
      have hgap_int :
          (2 : Int) ≤ (Int.natAbs (margin P1Profile y x - margin P1Profile z y) : Int) := by
        exact_mod_cast hgap_nat
      have hgap_abs :
          (2 : Int) ≤ |margin P1Profile y x - margin P1Profile z y| := by
        have hgap_int' := hgap_int
        rw [Int.natCast_natAbs] at hgap_int'
        simpa using hgap_int'
      have hmn_nonneg : 0 ≤ margin P1Profile y x - margin P1Profile z y := by
        linarith [hy z]
      have hgap :
          (2 : Int) ≤ margin P1Profile y x - margin P1Profile z y := by
        simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
      have hzlt : margin P1Profile z y < k := by
        linarith [hgap]
      simpa [hcard, hk] using hzlt
    · have hzle : margin P1Profile z y ≤ 0 := le_of_not_gt hzpos
      have hk_pos : 0 < k := by
        linarith [hm_ge2]
      have hzlt : margin P1Profile z y < k := by
        linarith [hzle, hk_pos]
      simpa [hcard, hk] using hzlt

lemma hgap_P3Profile {x y : A5}
    (hy : ∀ z, margin P3Profile z y < margin P3Profile y x) :
    ∃ W : Finset U450, Disjoint votersP3 W ∧
      (W.card : Int) < margin P3Profile y x ∧
      (∀ z, margin P3Profile z y < (W.card : Int)) := by
  classical
  have hmpos : 0 < margin P3Profile y x := by
    simpa [self_margin_zero] using (hy y)
  have hm_mem : margin P3Profile y x ∈ edgeWeights_P3 :=
    margin_P3Profile_pos_mem_edgeWeights (x := y) (y := x) hmpos
  set k : Int := margin P3Profile y x - 2 with hk
  have hk0 : 0 ≤ k := by
    have hm_ge : (6 : Int) ≤ margin P3Profile y x := edgeWeights_P3_ge_6 hm_mem
    linarith [hm_ge]
  have hk_le : k ≤ (170 : Int) := by
    have hm_le : margin P3Profile y x ≤ (170 : Int) := edgeWeights_P3_le_170 hm_mem
    linarith
  have hk_nat : k.toNat ≤ 170 := (Int.toNat_le (m := k) (n := 170)).2 hk_le
  obtain ⟨W, hdisj, hcard⟩ :=
    exists_disjoint_W_of_int_card_le_170 (V := votersP3)
      votersP3_subset_Iio_u280 hk0 hk_nat
  refine ⟨W, hdisj, ?_, ?_⟩
  · simp [hcard, hk]
  · intro z
    by_cases hzpos : 0 < margin P3Profile z y
    · have hz_mem : margin P3Profile z y ∈ edgeWeights_P3 :=
        margin_P3Profile_pos_mem_edgeWeights (x := z) (y := y) hzpos
      have hzlt : margin P3Profile z y < margin P3Profile y x := hy z
      have hne : margin P3Profile z y ≠ margin P3Profile y x := by linarith
      have hne' : margin P3Profile y x ≠ margin P3Profile z y := by
        exact ne_comm.mp hne
      have hgap_nat :
          4 ≤ Int.natAbs (margin P3Profile y x - margin P3Profile z y) :=
        edgeWeights_P3_gap4 _ hm_mem _ hz_mem hne'
      have hgap_int :
          (4 : Int) ≤ (Int.natAbs (margin P3Profile y x - margin P3Profile z y) : Int) := by
        exact_mod_cast hgap_nat
      have hgap_abs :
          (4 : Int) ≤ |margin P3Profile y x - margin P3Profile z y| := by
        have hgap_int' := hgap_int
        rw [Int.natCast_natAbs] at hgap_int'
        simpa using hgap_int'
      have hmn_nonneg : 0 ≤ margin P3Profile y x - margin P3Profile z y := by
        linarith [hzlt]
      have hgap :
          (4 : Int) ≤ margin P3Profile y x - margin P3Profile z y := by
        simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
      have hzlt' : margin P3Profile z y < margin P3Profile y x - 2 := by
        linarith [hgap]
      simpa [hcard, hk] using hzlt'
    · have hzle : margin P3Profile z y ≤ 0 := le_of_not_gt hzpos
      have hm_ge : (6 : Int) ≤ margin P3Profile y x := edgeWeights_P3_ge_6 hm_mem
      have hk_pos : 0 < k := by
        simp [hk]
        linarith [hm_ge]
      have hzlt : margin P3Profile z y < k := by linarith
      simpa [hcard, hk] using hzlt

lemma hgap_P5Profile {x y : A5}
    (hy : ∀ z, margin P5Profile z y < margin P5Profile y x) :
    ∃ W : Finset U450, Disjoint votersP5 W ∧
      (W.card : Int) < margin P5Profile y x ∧
      (∀ z, margin P5Profile z y < (W.card : Int)) := by
  classical
  have hmpos : 0 < margin P5Profile y x := by
    simpa [self_margin_zero] using (hy y)
  have hm_mem : margin P5Profile y x ∈ edgeWeights_P5 :=
    margin_P5Profile_pos_mem_edgeWeights (x := y) (y := x) hmpos
  set k : Int := margin P5Profile y x - 2 with hk
  have hk0 : 0 ≤ k := by
    have hm_ge : (6 : Int) ≤ margin P5Profile y x := edgeWeights_P5_ge_6 hm_mem
    linarith [hm_ge]
  have hk_le : k ≤ (170 : Int) := by
    have hm_le : margin P5Profile y x ≤ (170 : Int) := edgeWeights_P5_le_170 hm_mem
    linarith
  have hk_nat : k.toNat ≤ 170 := (Int.toNat_le (m := k) (n := 170)).2 hk_le
  obtain ⟨W, hdisj, hcard⟩ :=
    exists_disjoint_W_of_int_card_le_170 (V := votersP5)
      votersP5_subset_Iio_u280 hk0 hk_nat
  refine ⟨W, hdisj, ?_, ?_⟩
  · simp [hcard, hk]
  · intro z
    by_cases hzpos : 0 < margin P5Profile z y
    · have hz_mem : margin P5Profile z y ∈ edgeWeights_P5 :=
        margin_P5Profile_pos_mem_edgeWeights (x := z) (y := y) hzpos
      have hzlt : margin P5Profile z y < margin P5Profile y x := hy z
      have hne : margin P5Profile z y ≠ margin P5Profile y x := by linarith
      have hne' : margin P5Profile y x ≠ margin P5Profile z y := by
        exact ne_comm.mp hne
      have hgap_nat :
          6 ≤ Int.natAbs (margin P5Profile y x - margin P5Profile z y) :=
        edgeWeights_P5_gap6 _ hm_mem _ hz_mem hne'
      have hgap_int :
          (6 : Int) ≤ (Int.natAbs (margin P5Profile y x - margin P5Profile z y) : Int) := by
        exact_mod_cast hgap_nat
      have hgap_abs :
          (6 : Int) ≤ |margin P5Profile y x - margin P5Profile z y| := by
        have hgap_int' := hgap_int
        rw [Int.natCast_natAbs] at hgap_int'
        simpa using hgap_int'
      have hmn_nonneg : 0 ≤ margin P5Profile y x - margin P5Profile z y := by
        linarith [hzlt]
      have hgap :
          (6 : Int) ≤ margin P5Profile y x - margin P5Profile z y := by
        simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
      have hzlt' : margin P5Profile z y < margin P5Profile y x - 2 := by
        linarith [hgap]
      simpa [hcard, hk] using hzlt'
    · have hzle : margin P5Profile z y ≤ 0 := le_of_not_gt hzpos
      have hm_ge : (6 : Int) ≤ margin P5Profile y x := edgeWeights_P5_ge_6 hm_mem
      have hk_pos : 0 < k := by
        simp [hk]
        linarith [hm_ge]
      have hzlt : margin P5Profile z y < k := by linarith
      simpa [hcard, hk] using hzlt

end Holliday

end SocialChoice
