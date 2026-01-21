import Mathlib.Tactic
import SocialChoice.Margin
import SocialChoice.Impossibilities.Holliday.GapInstances

namespace SocialChoice

namespace Holliday

private lemma margin_add_newVoter_ge
    {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) :
    margin P a b - 1 ≤ margin Q a b := by
  have h : margin Q b a ≤ margin P b a + 1 :=
    margin_add_newVoter_le (hu := hu) P Q hagree b a
  have hskewP : margin P a b = - margin P b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a b
  have hskewQ : margin Q a b = - margin Q b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := Q)) a b
  linarith [h, hskewP, hskewQ]

lemma hgap_P3Profile_add_newVoter
    {u : U450} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v)
    {x y : A5} (hy : ∀ z, margin Q z y < margin Q y x) :
    ∃ W : Finset U450, Disjoint (insert u votersP3) W ∧
      (W.card : Int) < margin Q y x ∧
      (∀ z, margin Q z y < (W.card : Int)) := by
  classical
  have hmposQ : 0 < margin Q y x := by
    simpa [self_margin_zero] using (hy y)
  have hxy : x ≠ y := by
    intro hxy
    subst hxy
    simp [self_margin_zero] at hmposQ
  have hm_le : margin Q y x ≤ margin P3Profile y x + 1 :=
    margin_add_newVoter_le (hu := hu) P3Profile Q hagree y x
  have hm_ge0 : 0 ≤ margin P3Profile y x := by
    linarith [hmposQ, hm_le]
  have hm_ne0 : margin P3Profile y x ≠ 0 :=
    margin_P3Profile_ne_zero_of_ne (by exact ne_comm.mp hxy)
  have hmposP : 0 < margin P3Profile y x := by
    exact lt_of_le_of_ne hm_ge0 (Ne.symm hm_ne0)
  have hm_mem : margin P3Profile y x ∈ edgeWeights_P3 :=
    margin_P3Profile_pos_mem_edgeWeights (x := y) (y := x) hmposP
  set k : Int := margin P3Profile y x - 2 with hk
  have hk0 : 0 ≤ k := by
    have hm_ge : (6 : Int) ≤ margin P3Profile y x := edgeWeights_P3_ge_6 hm_mem
    linarith
  have hk_le : k ≤ (168 : Int) := by
    have hm_le' : margin P3Profile y x ≤ (107 : Int) := edgeWeights_P3_le_107 hm_mem
    linarith
  have hk_nat : k.toNat ≤ 168 := (Int.toNat_le (m := k) (n := 168)).2 hk_le
  obtain ⟨W, hdisj, hcard⟩ :=
    exists_disjoint_W_insert_of_int_card_le_168 (V := votersP3)
      votersP3_subset_Iio_u280 (u := u) hk0 hk_nat
  refine ⟨W, hdisj, ?_, ?_⟩
  · have hlow : margin P3Profile y x - 1 ≤ margin Q y x :=
      margin_add_newVoter_ge (hu := hu) P3Profile Q hagree y x
    have hklt : k < margin Q y x := by
      linarith [hlow]
    simpa [hcard, hk] using hklt
  · intro z
    by_cases hzposQ : 0 < margin Q z y
    · have hzy : z ≠ y := by
        intro hzy
        subst hzy
        simp [self_margin_zero] at hzposQ
      have hz_le : margin Q z y ≤ margin P3Profile z y + 1 :=
        margin_add_newVoter_le (hu := hu) P3Profile Q hagree z y
      have hz_ge : margin Q z y - 1 ≤ margin P3Profile z y := by
        linarith [hz_le]
      have hz_ge0 : 0 ≤ margin P3Profile z y := by
        linarith [hzposQ, hz_ge]
      have hz_ne0 : margin P3Profile z y ≠ 0 :=
        margin_P3Profile_ne_zero_of_ne hzy
      have hzposP : 0 < margin P3Profile z y := by
        exact lt_of_le_of_ne hz_ge0 (Ne.symm hz_ne0)
      have hz_mem : margin P3Profile z y ∈ edgeWeights_P3 :=
        margin_P3Profile_pos_mem_edgeWeights (x := z) (y := y) hzposP
      have hne : margin P3Profile y x ≠ margin P3Profile z y :=
        margin_P3Profile_pos_ne_pos (x := x) (y := y) (z := z) hmposP hzposP
      have hzleP : margin P3Profile z y ≤ margin P3Profile y x := by
        by_contra hzgt
        have hzgt' : margin P3Profile y x < margin P3Profile z y := lt_of_not_ge hzgt
        have hgap_nat :
            4 ≤ Int.natAbs (margin P3Profile z y - margin P3Profile y x) :=
          edgeWeights_P3_gap4 _ hz_mem _ hm_mem (by exact ne_comm.mp hne)
        have hgap_int :
            (4 : Int) ≤ (Int.natAbs (margin P3Profile z y - margin P3Profile y x) : Int) := by
          exact_mod_cast hgap_nat
        have hgap_abs :
            (4 : Int) ≤ |margin P3Profile z y - margin P3Profile y x| := by
          have hgap_int' := hgap_int
          rw [Int.natCast_natAbs] at hgap_int'
          simpa using hgap_int'
        have hmn_nonneg : 0 ≤ margin P3Profile z y - margin P3Profile y x := by
          linarith [hzgt']
        have hgap :
            (4 : Int) ≤ margin P3Profile z y - margin P3Profile y x := by
          simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
        have hlow' : margin P3Profile z y - 1 ≤ margin Q z y :=
          margin_add_newVoter_ge (hu := hu) P3Profile Q hagree z y
        have hhigh : margin Q y x ≤ margin P3Profile y x + 1 :=
          margin_add_newVoter_le (hu := hu) P3Profile Q hagree y x
        have hcontra : margin Q y x ≤ margin Q z y := by
          linarith [hgap, hlow', hhigh]
        exact (not_le_of_gt (hy z)) hcontra
      have hzltP : margin P3Profile z y < margin P3Profile y x := by
        exact lt_of_le_of_ne hzleP (Ne.symm hne)
      have hgap_nat :
          4 ≤ Int.natAbs (margin P3Profile y x - margin P3Profile z y) :=
        edgeWeights_P3_gap4 _ hm_mem _ hz_mem hne
      have hgap_int :
          (4 : Int) ≤ (Int.natAbs (margin P3Profile y x - margin P3Profile z y) : Int) := by
        exact_mod_cast hgap_nat
      have hgap_abs :
          (4 : Int) ≤ |margin P3Profile y x - margin P3Profile z y| := by
        have hgap_int' := hgap_int
        rw [Int.natCast_natAbs] at hgap_int'
        simpa using hgap_int'
      have hmn_nonneg : 0 ≤ margin P3Profile y x - margin P3Profile z y := by
        linarith [hzltP]
      have hgap :
          (4 : Int) ≤ margin P3Profile y x - margin P3Profile z y := by
        simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
      have hzlt' : margin Q z y < k := by
        linarith [hgap, hz_le]
      simpa [hcard, hk] using hzlt'
    · have hzle : margin Q z y ≤ 0 := le_of_not_gt hzposQ
      have hm_ge : (6 : Int) ≤ margin P3Profile y x := edgeWeights_P3_ge_6 hm_mem
      have hk_pos : 0 < k := by
        simp [hk]
        linarith [hm_ge]
      have hzlt : margin Q z y < k := by
        linarith [hzle, hk_pos]
      simpa [hcard, hk] using hzlt

lemma hgap_P5Profile_add_twoVoters
    {u2 u4 : U450} (hu2 : u2 ∉ votersP5) (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v)
    {x y : A5} (hy : ∀ z, margin Q z y < margin Q y x) :
    ∃ W : Finset U450, Disjoint (insert u4 (insert u2 votersP5)) W ∧
      (W.card : Int) < margin Q y x ∧
      (∀ z, margin Q z y < (W.card : Int)) := by
  classical
  have hmposQ : 0 < margin Q y x := by
    simpa [self_margin_zero] using (hy y)
  have hxy : x ≠ y := by
    intro hxy
    subst hxy
    simp [self_margin_zero] at hmposQ
  have hhigh1 : margin Q y x ≤ margin Q2 y x + 1 :=
    margin_add_newVoter_le (hu := hu4) Q2 Q hagree4 y x
  have hhigh2 : margin Q2 y x ≤ margin P5Profile y x + 1 :=
    margin_add_newVoter_le (hu := hu2) P5Profile Q2 hagree2 y x
  have hhigh : margin Q y x ≤ margin P5Profile y x + 2 := by
    linarith [hhigh1, hhigh2]
  have hmposP : 0 < margin P5Profile y x := by
    by_contra hnonpos
    have hle : margin P5Profile y x ≤ 0 := le_of_not_gt hnonpos
    have hm_ne0 : margin P5Profile y x ≠ 0 :=
      margin_P5Profile_ne_zero_of_ne (by exact ne_comm.mp hxy)
    have hlt : margin P5Profile y x < 0 := lt_of_le_of_ne hle hm_ne0
    have hposxy : 0 < margin P5Profile x y := by
      have h := margin_antisymmetric (P := P5Profile) x y
      linarith [hlt, h]
    have hmemxy : margin P5Profile x y ∈ edgeWeights_P5 :=
      margin_P5Profile_pos_mem_edgeWeights (x := x) (y := y) hposxy
    have hge : (6 : Int) ≤ margin P5Profile x y := edgeWeights_P5_ge_6 hmemxy
    have hneg : margin P5Profile y x ≤ (-6 : Int) := by
      have h := margin_antisymmetric (P := P5Profile) x y
      linarith [h, hge]
    have hcontra : margin Q y x ≤ (-4 : Int) := by
      linarith [hneg, hhigh]
    exact (not_le_of_gt hmposQ) (by linarith [hcontra])
  have hm_mem : margin P5Profile y x ∈ edgeWeights_P5 :=
    margin_P5Profile_pos_mem_edgeWeights (x := y) (y := x) hmposP
  set k : Int := margin P5Profile y x - 3 with hk
  have hk0 : 0 ≤ k := by
    have hm_ge : (6 : Int) ≤ margin P5Profile y x := edgeWeights_P5_ge_6 hm_mem
    linarith
  have hk_le : k ≤ (168 : Int) := by
    have hm_le' : margin P5Profile y x ≤ (138 : Int) := edgeWeights_P5_le_138 hm_mem
    linarith
  have hk_nat : k.toNat ≤ 168 := (Int.toNat_le (m := k) (n := 168)).2 hk_le
  obtain ⟨W, hdisj, hcard⟩ :=
    exists_disjoint_W_insert_insert_of_int_card_le_168 (V := votersP5)
      votersP5_subset_Iio_u280 (u1 := u4) (u2 := u2) hk0 hk_nat
  refine ⟨W, hdisj, ?_, ?_⟩
  · have hlow1 : margin P5Profile y x - 1 ≤ margin Q2 y x :=
      margin_add_newVoter_ge (hu := hu2) P5Profile Q2 hagree2 y x
    have hlow2 : margin Q2 y x - 1 ≤ margin Q y x :=
      margin_add_newVoter_ge (hu := hu4) Q2 Q hagree4 y x
    have hklt : k < margin Q y x := by
      linarith [hlow1, hlow2]
    simpa [hcard, hk] using hklt
  · intro z
    by_cases hzposQ : 0 < margin Q z y
    · have hzy : z ≠ y := by
        intro hzy
        subst hzy
        simp [self_margin_zero] at hzposQ
      have hz_le1 : margin Q z y ≤ margin Q2 z y + 1 :=
        margin_add_newVoter_le (hu := hu4) Q2 Q hagree4 z y
      have hz_le2 : margin Q2 z y ≤ margin P5Profile z y + 1 :=
        margin_add_newVoter_le (hu := hu2) P5Profile Q2 hagree2 z y
      have hz_le : margin Q z y ≤ margin P5Profile z y + 2 := by
        linarith [hz_le1, hz_le2]
      have hz_ge1 : margin Q z y - 1 ≤ margin Q2 z y := by
        linarith [hz_le1]
      have hz_ge2 : margin Q2 z y - 1 ≤ margin P5Profile z y := by
        linarith [hz_le2]
      have hz_ge : margin Q z y - 2 ≤ margin P5Profile z y := by
        linarith [hz_ge1, hz_ge2]
      have hzposP : 0 < margin P5Profile z y := by
        by_contra hznonpos
        have hzle : margin P5Profile z y ≤ 0 := le_of_not_gt hznonpos
        have hz_ne0 : margin P5Profile z y ≠ 0 :=
          margin_P5Profile_ne_zero_of_ne hzy
        have hzlt : margin P5Profile z y < 0 := lt_of_le_of_ne hzle hz_ne0
        have hposyz : 0 < margin P5Profile y z := by
          have h := margin_antisymmetric (P := P5Profile) y z
          linarith [hzlt, h]
        have hmemyz : margin P5Profile y z ∈ edgeWeights_P5 :=
          margin_P5Profile_pos_mem_edgeWeights (x := y) (y := z) hposyz
        have hge : (6 : Int) ≤ margin P5Profile y z := edgeWeights_P5_ge_6 hmemyz
        have hneg : margin P5Profile z y ≤ (-6 : Int) := by
          have h := margin_antisymmetric (P := P5Profile) y z
          linarith [h, hge]
        have hcontra : margin Q z y ≤ 0 := by
          linarith [hneg, hz_le]
        exact (not_le_of_gt hzposQ) hcontra
      have hz_mem : margin P5Profile z y ∈ edgeWeights_P5 :=
        margin_P5Profile_pos_mem_edgeWeights (x := z) (y := y) hzposP
      have hne : margin P5Profile y x ≠ margin P5Profile z y :=
        margin_P5Profile_pos_ne_pos (x := x) (y := y) (z := z) hmposP hzposP
      have hzleP : margin P5Profile z y ≤ margin P5Profile y x := by
        by_contra hzgt
        have hzgt' : margin P5Profile y x < margin P5Profile z y := lt_of_not_ge hzgt
        have hgap_nat :
            6 ≤ Int.natAbs (margin P5Profile z y - margin P5Profile y x) :=
          edgeWeights_P5_gap6 _ hz_mem _ hm_mem (by exact ne_comm.mp hne)
        have hgap_int :
            (6 : Int) ≤ (Int.natAbs (margin P5Profile z y - margin P5Profile y x) : Int) := by
          exact_mod_cast hgap_nat
        have hgap_abs :
            (6 : Int) ≤ |margin P5Profile z y - margin P5Profile y x| := by
          have hgap_int' := hgap_int
          rw [Int.natCast_natAbs] at hgap_int'
          simpa using hgap_int'
        have hmn_nonneg : 0 ≤ margin P5Profile z y - margin P5Profile y x := by
          linarith [hzgt']
        have hgap :
            (6 : Int) ≤ margin P5Profile z y - margin P5Profile y x := by
          simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
        have hlow1 : margin P5Profile z y - 1 ≤ margin Q2 z y :=
          margin_add_newVoter_ge (hu := hu2) P5Profile Q2 hagree2 z y
        have hlow2 : margin Q2 z y - 1 ≤ margin Q z y :=
          margin_add_newVoter_ge (hu := hu4) Q2 Q hagree4 z y
        have hlow' : margin P5Profile z y - 2 ≤ margin Q z y := by
          linarith [hlow1, hlow2]
        have hcontra : margin Q y x ≤ margin Q z y := by
          linarith [hgap, hlow', hhigh]
        exact (not_le_of_gt (hy z)) hcontra
      have hzltP : margin P5Profile z y < margin P5Profile y x := by
        exact lt_of_le_of_ne hzleP (Ne.symm hne)
      have hgap_nat :
          6 ≤ Int.natAbs (margin P5Profile y x - margin P5Profile z y) :=
        edgeWeights_P5_gap6 _ hm_mem _ hz_mem hne
      have hgap_int :
          (6 : Int) ≤ (Int.natAbs (margin P5Profile y x - margin P5Profile z y) : Int) := by
        exact_mod_cast hgap_nat
      have hgap_abs :
          (6 : Int) ≤ |margin P5Profile y x - margin P5Profile z y| := by
        have hgap_int' := hgap_int
        rw [Int.natCast_natAbs] at hgap_int'
        simpa using hgap_int'
      have hmn_nonneg : 0 ≤ margin P5Profile y x - margin P5Profile z y := by
        linarith [hzltP]
      have hgap :
          (6 : Int) ≤ margin P5Profile y x - margin P5Profile z y := by
        simpa [abs_of_nonneg hmn_nonneg] using hgap_abs
      have hzlt' : margin Q z y < k := by
        linarith [hgap, hz_le]
      simpa [hcard, hk] using hzlt'
    · have hzle : margin Q z y ≤ 0 := le_of_not_gt hzposQ
      have hm_ge : (6 : Int) ≤ margin P5Profile y x := edgeWeights_P5_ge_6 hm_mem
      have hk_pos : 0 < k := by
        simp [hk]
        linarith [hm_ge]
      have hzlt : margin Q z y < k := by
        linarith [hzle, hk_pos]
      simpa [hcard, hk] using hzlt

end Holliday

end SocialChoice
