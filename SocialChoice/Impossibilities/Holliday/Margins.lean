import SocialChoice.Impossibilities.Holliday.Profiles

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

lemma sum_marginOfBallot_const (S : Finset U450) (ballot : ListBallot 5) (a b : A5)
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

lemma margin_restrictElectorate_eq_sum_marginOfBallot (S : Finset U450) {a b : A5} (hne : a ≠ b) :
    margin (restrictElectorate FullProfile S (by intro x _; exact Finset.mem_univ x)) a b =
      S.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
  classical
  set P := restrictElectorate FullProfile S (by intro x _; exact Finset.mem_univ x) with hP
  have hpref :
      ∀ v : Electorate U450 S,
        Prefers P v a b ↔ prefersInList (ballotsAll v.1).ranking a b = true := by
    intro v
    simpa [hP] using
      (prefers_restrictElectorate_iff_prefersInList (S := S) (v := v) (a := a) (b := b))
  have hpref_ba :
      ∀ v : Electorate U450 S,
        Prefers P v b a ↔ prefersInList (ballotsAll v.1).ranking b a = true := by
    intro v
    simpa [hP] using
      (prefers_restrictElectorate_iff_prefersInList (S := S) (v := v) (a := b) (b := a))
  have hcount_ab :
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S => Prefers P v a b)).card) =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) := by
    calc
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S => Prefers P v a b)).card) =
          (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S =>
            prefersInList (ballotsAll v.1).ranking a b = true)).card) := by
            simp [hpref]
      _ = (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
            if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) := by
            simp
  have hcount_ba :
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S => Prefers P v b a)).card) =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) := by
    calc
      (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S => Prefers P v b a)).card) =
          (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S =>
            prefersInList (ballotsAll v.1).ranking b a = true)).card) := by
            simp [hpref_ba]
      _ = (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
            if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) := by
            simp
  have hsum :
      (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          (if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
            (if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0)) := by
    symm
    exact Finset.sum_sub_distrib _ _
  have hsum' :
      (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          (if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
            (if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0)) =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := by
    refine Finset.sum_congr rfl ?_
    intro v _hv
    simp [marginOfBallot_eq_sub_indicators (b := ballotsAll v.1) (hne := hne)]
  have hmargin :
      margin P a b =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := by
    calc
      margin P a b =
          (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S => Prefers P v a b)).card) -
            (Int.ofNat (Finset.univ.filter (fun v : Electorate U450 S => Prefers P v b a)).card) := by
          simp [margin, hP]
      _ =
          (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
              if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
            (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
              if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0) := by
          rw [hcount_ab, hcount_ba]
      _ =
          (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
            (if prefersInList (ballotsAll v.1).ranking a b = true then (1 : Int) else 0) -
              (if prefersInList (ballotsAll v.1).ranking b a = true then (1 : Int) else 0)) := hsum
      _ = (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
            marginOfBallot (ballotsAll v.1) a b) := hsum'
  have hsum_subtype :
      S.sum (fun v => marginOfBallot (ballotsAll v) a b) =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := by
    refine (Finset.sum_subtype (s := S) (p := fun v => v ∈ S) ?_
      (f := fun v => marginOfBallot (ballotsAll v) a b))
    intro x
    simp
  calc
    margin P a b =
        (Finset.univ : Finset (Electorate U450 S)).sum (fun v =>
          marginOfBallot (ballotsAll v.1) a b) := hmargin
    _ = S.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
        symm
        simp [hsum_subtype]

lemma sum_Ico_marginOfBallot_of_mem_block (a b : A5) {lo hi : U450} {ballot : ListBallot 5} :
    (lo.val, hi.val, ballot) ∈ ballotsAllBlocks →
    (Finset.Ico lo hi).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      ((Finset.Ico lo hi).card : Int) * marginOfBallot ballot a b := by
  intro hmem
  refine sum_marginOfBallot_const (S := Finset.Ico lo hi) (ballot := ballot) (a := a) (b := b) ?_
  intro v hv
  have hv' : lo.val ≤ v.val ∧ v.val < hi.val := by
    rcases (Finset.mem_Ico.mp hv) with ⟨hlo, hhi⟩
    exact ⟨Fin.le_def.mp hlo, Fin.lt_def.mp hhi⟩
  exact ballotsAll_eq_of_mem_block (v := v) hmem hv'.1 hv'.2

@[simp] lemma sum_Ico_marginOfBallot_p1_1 (a b : A5) :
    (Finset.Ico (0 : U450) p1_cut1_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (63 : Int) * marginOfBallot ballot_daceb a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := 0) (hi := p1_cut1_fin)
      (ballot := ballot_daceb) (by simp [p1_cut1_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_2 (a b : A5) :
    (Finset.Ico p1_cut1_fin p1_cut2_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (6 : Int) * marginOfBallot ballot_daceb a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut1_fin) (hi := p1_cut2_fin)
      (ballot := ballot_daceb) (by simp [p1_cut1_fin, p1_cut2_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_3 (a b : A5) :
    (Finset.Ico p1_cut2_fin p1_cut3_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (67 : Int) * marginOfBallot ballot_ebacd a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut2_fin) (hi := p1_cut3_fin)
      (ballot := ballot_ebacd) (by simp [p1_cut2_fin, p1_cut3_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_4 (a b : A5) :
    (Finset.Ico p1_cut3_fin p1_cut4_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (27 : Int) * marginOfBallot ballot_bcaed a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut3_fin) (hi := p1_cut4_fin)
      (ballot := ballot_bcaed) (by simp [p1_cut3_fin, p1_cut4_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_5 (a b : A5) :
    (Finset.Ico p1_cut4_fin p1_cut5_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (21 : Int) * marginOfBallot ballot_cedba a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut4_fin) (hi := p1_cut5_fin)
      (ballot := ballot_cedba) (by simp [p1_cut4_fin, p1_cut5_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_6 (a b : A5) :
    (Finset.Ico p1_cut5_fin p1_cut6_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (13 : Int) * marginOfBallot ballot_dbcae a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut5_fin) (hi := p1_cut6_fin)
      (ballot := ballot_dbcae) (by simp [p1_cut5_fin, p1_cut6_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_7 (a b : A5) :
    (Finset.Ico p1_cut6_fin p1_cut7_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (7 : Int) * marginOfBallot ballot_dbcae a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut6_fin) (hi := p1_cut7_fin)
      (ballot := ballot_dbcae) (by simp [p1_cut6_fin, p1_cut7_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_8 (a b : A5) :
    (Finset.Ico p1_cut7_fin p1_cut8_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (18 : Int) * marginOfBallot ballot_bacde a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut7_fin) (hi := p1_cut8_fin)
      (ballot := ballot_bacde) (by simp [p1_cut7_fin, p1_cut8_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_9 (a b : A5) :
    (Finset.Ico p1_cut8_fin p1_cut9_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (27 : Int) * marginOfBallot ballot_adbec a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut8_fin) (hi := p1_cut9_fin)
      (ballot := ballot_adbec) (by simp [p1_cut8_fin, p1_cut9_fin]))
  simp [Fin.card_Ico] at h
  exact h

@[simp] lemma sum_Ico_marginOfBallot_p1_10 (a b : A5) :
    (Finset.Ico p1_cut9_fin p1_cut10_fin).sum (fun v => marginOfBallot (ballotsAll v) a b) =
      (24 : Int) * marginOfBallot ballot_bdeac a b := by
  have h :=
    (sum_Ico_marginOfBallot_of_mem_block (a := a) (b := b) (lo := p1_cut9_fin)
      (hi := p1_cut10_fin) (ballot := ballot_bdeac) (by simp [p1_cut9_fin, p1_cut10_fin]))
  simp [Fin.card_Ico] at h
  exact h

lemma votersP1_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP1.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP1 a b := by
  classical
  let f : U450 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum : votersP1.sum f = marginBlocks blocksP1 a b := by
    simp [f, votersP1_eq_Ico, sum_Ico_chain_p1, p1_cut_list, sum_Ico_chain,
      marginBlocks, blocksP1]
    ring_nf
  simpa using hsum

lemma votersP2_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP2.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP2 a b := by
  classical
  let f : U450 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum : votersP2.sum f = votersP1.sum f + votersP1_9.sum f := by
    simp [votersP2_eq_Ico, votersP1_eq_Ico, votersP1_9, sum_Ico_chain_p1_9, sum_Ico_chain]
  calc
    votersP2.sum f = votersP1.sum f + votersP1_9.sum f := hsum
    _ = marginBlocks blocksP2 a b := by
      simp [f, votersP1_sum_marginOfBallot_eq_marginBlocks, votersP1_9,
        marginBlocks, blocksP2, blocksP1]

lemma votersP3_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP3.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP3 a b := by
  classical
  let f : U450 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum_sdiff :
      (votersP2 \ votersP1_2).sum f = votersP2.sum f - votersP1_2.sum f := by
    simpa using
      (Finset.sum_sdiff_eq_sub (s₁ := votersP1_2) (s₂ := votersP2) (f := f)
        votersP1_2_subset_votersP2)
  calc
    votersP3.sum f = (votersP2 \ votersP1_2).sum f := by
      simp [votersP3_eq_sdiff]
    _ = votersP2.sum f - votersP1_2.sum f := hsum_sdiff
    _ = marginBlocks blocksP3 a b := by
      simp [f, votersP2_sum_marginOfBallot_eq_marginBlocks, votersP1_2,
        marginBlocks, blocksP3, blocksP2, blocksP1]
      ring_nf

lemma votersP4_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP4.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP4 a b := by
  classical
  let f : U450 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum_sdiff :
      (votersP2 \ votersP1_2).sum f = votersP2.sum f - votersP1_2.sum f := by
    simpa using
      (Finset.sum_sdiff_eq_sub (s₁ := votersP1_2) (s₂ := votersP2) (f := f)
        votersP1_2_subset_votersP2)
  have hdisj : Disjoint (votersP2 \ votersP1_2) votersP1_10 := by
    refine Finset.disjoint_left.2 ?_
    intro v hv2 hv14
    have hv2' : v.val < p1_cut9 := by
      simpa [votersP2] using (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv2).1).2
    have hv14' : p1_cut9 ≤ v.val := by
      have hv14' : p1_cut9 ≤ v.val ∧ v.val < p1_cut10 := by
        simpa [votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def,
          p1_cut9_fin, p1_cut10_fin] using hv14
      exact hv14'.1
    exact (not_lt_of_ge hv14') hv2'
  have hsum_union :
      votersP4.sum f = (votersP2 \ votersP1_2).sum f + votersP1_10.sum f := by
    simpa [votersP4_eq_union_sdiff] using
      (Finset.sum_union (s₁ := votersP2 \ votersP1_2) (s₂ := votersP1_10) (f := f) hdisj)
  calc
    votersP4.sum f = (votersP2 \ votersP1_2).sum f + votersP1_10.sum f := hsum_union
    _ = (votersP2.sum f - votersP1_2.sum f) + votersP1_10.sum f := by
        simp [hsum_sdiff]
    _ = marginBlocks blocksP4 a b := by
        simp [f, votersP2_sum_marginOfBallot_eq_marginBlocks, votersP1_2, votersP1_10,
          marginBlocks, blocksP4, blocksP3, blocksP2, blocksP1]
        ring_nf

lemma votersP5_sum_marginOfBallot_eq_marginBlocks (a b : A5) :
    votersP5.sum (fun v => marginOfBallot (ballotsAll v) a b) = marginBlocks blocksP5 a b := by
  classical
  let f : U450 → Int := fun v => marginOfBallot (ballotsAll v) a b
  have hsum_sdiff :
      (votersP4 \ votersP1_7).sum f = votersP4.sum f - votersP1_7.sum f := by
    simpa using
      (Finset.sum_sdiff_eq_sub (s₁ := votersP1_7) (s₂ := votersP4) (f := f)
        votersP1_7_subset_votersP4)
  calc
    votersP5.sum f = (votersP4 \ votersP1_7).sum f := by
      simp [votersP5_eq_sdiff]
    _ = votersP4.sum f - votersP1_7.sum f := hsum_sdiff
    _ = marginBlocks blocksP5 a b := by
      simp [f, votersP4_sum_marginOfBallot_eq_marginBlocks, votersP1_7,
        marginBlocks, blocksP5, blocksP4, blocksP3]
      ring_nf

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

lemma margin_P3Profile_eq_blocks {a b : A5} (hne : a ≠ b) :
    margin P3Profile a b = marginBlocks blocksP3 a b := by
  calc
    margin P3Profile a b =
        votersP3.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
      simpa [P3Profile] using
        (margin_restrictElectorate_eq_sum_marginOfBallot (S := votersP3) (a := a) (b := b) (hne := hne))
    _ = marginBlocks blocksP3 a b := votersP3_sum_marginOfBallot_eq_marginBlocks (a := a) (b := b)

lemma margin_P4Profile_eq_blocks {a b : A5} (hne : a ≠ b) :
    margin P4Profile a b = marginBlocks blocksP4 a b := by
  calc
    margin P4Profile a b =
        votersP4.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
      simpa [P4Profile] using
        (margin_restrictElectorate_eq_sum_marginOfBallot (S := votersP4) (a := a) (b := b) (hne := hne))
    _ = marginBlocks blocksP4 a b := votersP4_sum_marginOfBallot_eq_marginBlocks (a := a) (b := b)

lemma margin_P5Profile_eq_blocks {a b : A5} (hne : a ≠ b) :
    margin P5Profile a b = marginBlocks blocksP5 a b := by
  calc
    margin P5Profile a b =
        votersP5.sum (fun v => marginOfBallot (ballotsAll v) a b) := by
      simpa [P5Profile] using
        (margin_restrictElectorate_eq_sum_marginOfBallot (S := votersP5) (a := a) (b := b) (hne := hne))
    _ = marginBlocks blocksP5 a b := votersP5_sum_marginOfBallot_eq_marginBlocks (a := a) (b := b)

lemma marginBlocks_P1_a_b : marginBlocks blocksP1 a b = (-84 : Int) := by
  decide

lemma marginBlocks_P1_a_c : marginBlocks blocksP1 a c = 86 := by
  decide

lemma marginBlocks_P1_a_d : marginBlocks blocksP1 a d = 2 := by
  decide

lemma marginBlocks_P1_a_e : marginBlocks blocksP1 a e = 46 := by
  decide

lemma marginBlocks_P1_b_c : marginBlocks blocksP1 b c = 42 := by
  decide

lemma marginBlocks_P1_b_d : marginBlocks blocksP1 b d = 2 := by
  decide

lemma marginBlocks_P1_b_e : marginBlocks blocksP1 b e = (-92 : Int) := by
  decide

lemma marginBlocks_P1_c_d : marginBlocks blocksP1 c d = 44 := by
  decide

lemma marginBlocks_P1_c_e : marginBlocks blocksP1 c e = 88 := by
  decide

lemma marginBlocks_P1_d_e : marginBlocks blocksP1 d e = (-8 : Int) := by
  decide

lemma marginBlocks_P2_a_b : marginBlocks blocksP2 a b = (-57 : Int) := by
  decide

lemma marginBlocks_P2_a_c : marginBlocks blocksP2 a c = 113 := by
  decide

lemma marginBlocks_P2_a_d : marginBlocks blocksP2 a d = 29 := by
  decide

lemma marginBlocks_P2_a_e : marginBlocks blocksP2 a e = 73 := by
  decide

lemma marginBlocks_P2_b_c : marginBlocks blocksP2 b c = 69 := by
  decide

lemma marginBlocks_P2_b_d : marginBlocks blocksP2 b d = (-25 : Int) := by
  decide

lemma marginBlocks_P2_b_e : marginBlocks blocksP2 b e = (-65 : Int) := by
  decide

lemma marginBlocks_P2_c_d : marginBlocks blocksP2 c d = 17 := by
  decide

lemma marginBlocks_P2_c_e : marginBlocks blocksP2 c e = 61 := by
  decide

lemma marginBlocks_P2_d_e : marginBlocks blocksP2 d e = 19 := by
  decide

lemma marginBlocks_P3_a_b : marginBlocks blocksP3 a b = (-63 : Int) := by
  decide

lemma marginBlocks_P3_a_c : marginBlocks blocksP3 a c = 107 := by
  decide

lemma marginBlocks_P3_a_d : marginBlocks blocksP3 a d = 35 := by
  decide

lemma marginBlocks_P3_a_e : marginBlocks blocksP3 a e = 67 := by
  decide

lemma marginBlocks_P3_b_c : marginBlocks blocksP3 b c = 75 := by
  decide

lemma marginBlocks_P3_b_d : marginBlocks blocksP3 b d = (-19 : Int) := by
  decide

lemma marginBlocks_P3_b_e : marginBlocks blocksP3 b e = (-59 : Int) := by
  decide

lemma marginBlocks_P3_c_d : marginBlocks blocksP3 c d = 23 := by
  decide

lemma marginBlocks_P3_c_e : marginBlocks blocksP3 c e = 55 := by
  decide

lemma marginBlocks_P3_d_e : marginBlocks blocksP3 d e = 13 := by
  decide

lemma marginBlocks_P4_a_b : marginBlocks blocksP4 a b = (-87 : Int) := by
  decide

lemma marginBlocks_P4_a_c : marginBlocks blocksP4 a c = 131 := by
  decide

lemma marginBlocks_P4_a_d : marginBlocks blocksP4 a d = 11 := by
  decide

lemma marginBlocks_P4_a_e : marginBlocks blocksP4 a e = 43 := by
  decide

lemma marginBlocks_P4_b_c : marginBlocks blocksP4 b c = 99 := by
  decide

lemma marginBlocks_P4_b_d : marginBlocks blocksP4 b d = 5 := by
  decide

lemma marginBlocks_P4_b_e : marginBlocks blocksP4 b e = (-35 : Int) := by
  decide

lemma marginBlocks_P4_c_d : marginBlocks blocksP4 c d = (-1 : Int) := by
  decide

lemma marginBlocks_P4_c_e : marginBlocks blocksP4 c e = 31 := by
  decide

lemma marginBlocks_P4_d_e : marginBlocks blocksP4 d e = 37 := by
  decide

lemma marginBlocks_P5_a_b : marginBlocks blocksP5 a b = (-80 : Int) := by
  decide

lemma marginBlocks_P5_a_c : marginBlocks blocksP5 a c = 138 := by
  decide

lemma marginBlocks_P5_a_d : marginBlocks blocksP5 a d = 18 := by
  decide

lemma marginBlocks_P5_a_e : marginBlocks blocksP5 a e = 36 := by
  decide

lemma marginBlocks_P5_b_c : marginBlocks blocksP5 b c = 92 := by
  decide

lemma marginBlocks_P5_b_d : marginBlocks blocksP5 b d = 12 := by
  decide

lemma marginBlocks_P5_b_e : marginBlocks blocksP5 b e = (-42 : Int) := by
  decide

lemma marginBlocks_P5_c_d : marginBlocks blocksP5 c d = 6 := by
  decide

lemma marginBlocks_P5_c_e : marginBlocks blocksP5 c e = 24 := by
  decide

lemma marginBlocks_P5_d_e : marginBlocks blocksP5 d e = 30 := by
  decide

lemma margin_P1Profile_a_b : margin P1Profile a b = (-84 : Int) := by
  calc
    margin P1Profile a b = marginBlocks blocksP1 a b := margin_P1Profile_eq_blocks (a := a) (b := b)
      (by decide)
    _ = (-84 : Int) := by simpa using marginBlocks_P1_a_b

lemma margin_P1Profile_a_c : margin P1Profile a c = 86 := by
  calc
    margin P1Profile a c = marginBlocks blocksP1 a c := margin_P1Profile_eq_blocks (a := a) (b := c)
      (by decide)
    _ = 86 := by simpa using marginBlocks_P1_a_c

lemma margin_P1Profile_a_d : margin P1Profile a d = 2 := by
  calc
    margin P1Profile a d = marginBlocks blocksP1 a d := margin_P1Profile_eq_blocks (a := a) (b := d)
      (by decide)
    _ = 2 := by simpa using marginBlocks_P1_a_d

lemma margin_P1Profile_a_e : margin P1Profile a e = 46 := by
  calc
    margin P1Profile a e = marginBlocks blocksP1 a e := margin_P1Profile_eq_blocks (a := a) (b := e)
      (by decide)
    _ = 46 := by simpa using marginBlocks_P1_a_e

lemma margin_P1Profile_b_c : margin P1Profile b c = 42 := by
  calc
    margin P1Profile b c = marginBlocks blocksP1 b c := margin_P1Profile_eq_blocks (a := b) (b := c)
      (by decide)
    _ = 42 := by simpa using marginBlocks_P1_b_c

lemma margin_P1Profile_b_d : margin P1Profile b d = 2 := by
  calc
    margin P1Profile b d = marginBlocks blocksP1 b d := margin_P1Profile_eq_blocks (a := b) (b := d)
      (by decide)
    _ = 2 := by simpa using marginBlocks_P1_b_d

lemma margin_P1Profile_b_e : margin P1Profile b e = (-92 : Int) := by
  calc
    margin P1Profile b e = marginBlocks blocksP1 b e := margin_P1Profile_eq_blocks (a := b) (b := e)
      (by decide)
    _ = (-92 : Int) := by simpa using marginBlocks_P1_b_e

lemma margin_P1Profile_c_d : margin P1Profile c d = 44 := by
  calc
    margin P1Profile c d = marginBlocks blocksP1 c d := margin_P1Profile_eq_blocks (a := c) (b := d)
      (by decide)
    _ = 44 := by simpa using marginBlocks_P1_c_d

lemma margin_P1Profile_c_e : margin P1Profile c e = 88 := by
  calc
    margin P1Profile c e = marginBlocks blocksP1 c e := margin_P1Profile_eq_blocks (a := c) (b := e)
      (by decide)
    _ = 88 := by simpa using marginBlocks_P1_c_e

lemma margin_P1Profile_d_e : margin P1Profile d e = (-8 : Int) := by
  calc
    margin P1Profile d e = marginBlocks blocksP1 d e := margin_P1Profile_eq_blocks (a := d) (b := e)
      (by decide)
    _ = (-8 : Int) := by simpa using marginBlocks_P1_d_e

lemma margin_P2Profile_a_b : margin P2Profile a b = (-57 : Int) := by
  calc
    margin P2Profile a b = marginBlocks blocksP2 a b := margin_P2Profile_eq_blocks (a := a) (b := b)
      (by decide)
    _ = (-57 : Int) := by simpa using marginBlocks_P2_a_b

lemma margin_P2Profile_a_c : margin P2Profile a c = 113 := by
  calc
    margin P2Profile a c = marginBlocks blocksP2 a c := margin_P2Profile_eq_blocks (a := a) (b := c)
      (by decide)
    _ = 113 := by simpa using marginBlocks_P2_a_c

lemma margin_P2Profile_a_d : margin P2Profile a d = 29 := by
  calc
    margin P2Profile a d = marginBlocks blocksP2 a d := margin_P2Profile_eq_blocks (a := a) (b := d)
      (by decide)
    _ = 29 := by simpa using marginBlocks_P2_a_d

lemma margin_P2Profile_a_e : margin P2Profile a e = 73 := by
  calc
    margin P2Profile a e = marginBlocks blocksP2 a e := margin_P2Profile_eq_blocks (a := a) (b := e)
      (by decide)
    _ = 73 := by simpa using marginBlocks_P2_a_e

lemma margin_P2Profile_b_c : margin P2Profile b c = 69 := by
  calc
    margin P2Profile b c = marginBlocks blocksP2 b c := margin_P2Profile_eq_blocks (a := b) (b := c)
      (by decide)
    _ = 69 := by simpa using marginBlocks_P2_b_c

lemma margin_P2Profile_b_d : margin P2Profile b d = (-25 : Int) := by
  calc
    margin P2Profile b d = marginBlocks blocksP2 b d := margin_P2Profile_eq_blocks (a := b) (b := d)
      (by decide)
    _ = (-25 : Int) := by simpa using marginBlocks_P2_b_d

lemma margin_P2Profile_b_e : margin P2Profile b e = (-65 : Int) := by
  calc
    margin P2Profile b e = marginBlocks blocksP2 b e := margin_P2Profile_eq_blocks (a := b) (b := e)
      (by decide)
    _ = (-65 : Int) := by simpa using marginBlocks_P2_b_e

lemma margin_P2Profile_c_d : margin P2Profile c d = 17 := by
  calc
    margin P2Profile c d = marginBlocks blocksP2 c d := margin_P2Profile_eq_blocks (a := c) (b := d)
      (by decide)
    _ = 17 := by simpa using marginBlocks_P2_c_d

lemma margin_P2Profile_c_e : margin P2Profile c e = 61 := by
  calc
    margin P2Profile c e = marginBlocks blocksP2 c e := margin_P2Profile_eq_blocks (a := c) (b := e)
      (by decide)
    _ = 61 := by simpa using marginBlocks_P2_c_e

lemma margin_P2Profile_d_e : margin P2Profile d e = 19 := by
  calc
    margin P2Profile d e = marginBlocks blocksP2 d e := margin_P2Profile_eq_blocks (a := d) (b := e)
      (by decide)
    _ = 19 := by simpa using marginBlocks_P2_d_e

lemma margin_P3Profile_a_b : margin P3Profile a b = (-63 : Int) := by
  calc
    margin P3Profile a b = marginBlocks blocksP3 a b := margin_P3Profile_eq_blocks (a := a) (b := b)
      (by decide)
    _ = (-63 : Int) := by simpa using marginBlocks_P3_a_b

lemma margin_P3Profile_a_c : margin P3Profile a c = 107 := by
  calc
    margin P3Profile a c = marginBlocks blocksP3 a c := margin_P3Profile_eq_blocks (a := a) (b := c)
      (by decide)
    _ = 107 := by simpa using marginBlocks_P3_a_c

lemma margin_P3Profile_a_d : margin P3Profile a d = 35 := by
  calc
    margin P3Profile a d = marginBlocks blocksP3 a d := margin_P3Profile_eq_blocks (a := a) (b := d)
      (by decide)
    _ = 35 := by simpa using marginBlocks_P3_a_d

lemma margin_P3Profile_a_e : margin P3Profile a e = 67 := by
  calc
    margin P3Profile a e = marginBlocks blocksP3 a e := margin_P3Profile_eq_blocks (a := a) (b := e)
      (by decide)
    _ = 67 := by simpa using marginBlocks_P3_a_e

lemma margin_P3Profile_b_c : margin P3Profile b c = 75 := by
  calc
    margin P3Profile b c = marginBlocks blocksP3 b c := margin_P3Profile_eq_blocks (a := b) (b := c)
      (by decide)
    _ = 75 := by simpa using marginBlocks_P3_b_c

lemma margin_P3Profile_b_d : margin P3Profile b d = (-19 : Int) := by
  calc
    margin P3Profile b d = marginBlocks blocksP3 b d := margin_P3Profile_eq_blocks (a := b) (b := d)
      (by decide)
    _ = (-19 : Int) := by simpa using marginBlocks_P3_b_d

lemma margin_P3Profile_b_e : margin P3Profile b e = (-59 : Int) := by
  calc
    margin P3Profile b e = marginBlocks blocksP3 b e := margin_P3Profile_eq_blocks (a := b) (b := e)
      (by decide)
    _ = (-59 : Int) := by simpa using marginBlocks_P3_b_e

lemma margin_P3Profile_c_d : margin P3Profile c d = 23 := by
  calc
    margin P3Profile c d = marginBlocks blocksP3 c d := margin_P3Profile_eq_blocks (a := c) (b := d)
      (by decide)
    _ = 23 := by simpa using marginBlocks_P3_c_d

lemma margin_P3Profile_c_e : margin P3Profile c e = 55 := by
  calc
    margin P3Profile c e = marginBlocks blocksP3 c e := margin_P3Profile_eq_blocks (a := c) (b := e)
      (by decide)
    _ = 55 := by simpa using marginBlocks_P3_c_e

lemma margin_P3Profile_d_e : margin P3Profile d e = 13 := by
  calc
    margin P3Profile d e = marginBlocks blocksP3 d e := margin_P3Profile_eq_blocks (a := d) (b := e)
      (by decide)
    _ = 13 := by simpa using marginBlocks_P3_d_e

lemma margin_P4Profile_a_b : margin P4Profile a b = (-87 : Int) := by
  calc
    margin P4Profile a b = marginBlocks blocksP4 a b := margin_P4Profile_eq_blocks (a := a) (b := b)
      (by decide)
    _ = (-87 : Int) := by simpa using marginBlocks_P4_a_b

lemma margin_P4Profile_a_c : margin P4Profile a c = 131 := by
  calc
    margin P4Profile a c = marginBlocks blocksP4 a c := margin_P4Profile_eq_blocks (a := a) (b := c)
      (by decide)
    _ = 131 := by simpa using marginBlocks_P4_a_c

lemma margin_P4Profile_a_d : margin P4Profile a d = 11 := by
  calc
    margin P4Profile a d = marginBlocks blocksP4 a d := margin_P4Profile_eq_blocks (a := a) (b := d)
      (by decide)
    _ = 11 := by simpa using marginBlocks_P4_a_d

lemma margin_P4Profile_a_e : margin P4Profile a e = 43 := by
  calc
    margin P4Profile a e = marginBlocks blocksP4 a e := margin_P4Profile_eq_blocks (a := a) (b := e)
      (by decide)
    _ = 43 := by simpa using marginBlocks_P4_a_e

lemma margin_P4Profile_b_c : margin P4Profile b c = 99 := by
  calc
    margin P4Profile b c = marginBlocks blocksP4 b c := margin_P4Profile_eq_blocks (a := b) (b := c)
      (by decide)
    _ = 99 := by simpa using marginBlocks_P4_b_c

lemma margin_P4Profile_b_d : margin P4Profile b d = 5 := by
  calc
    margin P4Profile b d = marginBlocks blocksP4 b d := margin_P4Profile_eq_blocks (a := b) (b := d)
      (by decide)
    _ = 5 := by simpa using marginBlocks_P4_b_d

lemma margin_P4Profile_b_e : margin P4Profile b e = (-35 : Int) := by
  calc
    margin P4Profile b e = marginBlocks blocksP4 b e := margin_P4Profile_eq_blocks (a := b) (b := e)
      (by decide)
    _ = (-35 : Int) := by simpa using marginBlocks_P4_b_e

lemma margin_P4Profile_c_d : margin P4Profile c d = (-1 : Int) := by
  calc
    margin P4Profile c d = marginBlocks blocksP4 c d := margin_P4Profile_eq_blocks (a := c) (b := d)
      (by decide)
    _ = (-1 : Int) := by simpa using marginBlocks_P4_c_d

lemma margin_P4Profile_c_e : margin P4Profile c e = 31 := by
  calc
    margin P4Profile c e = marginBlocks blocksP4 c e := margin_P4Profile_eq_blocks (a := c) (b := e)
      (by decide)
    _ = 31 := by simpa using marginBlocks_P4_c_e

lemma margin_P4Profile_d_e : margin P4Profile d e = 37 := by
  calc
    margin P4Profile d e = marginBlocks blocksP4 d e := margin_P4Profile_eq_blocks (a := d) (b := e)
      (by decide)
    _ = 37 := by simpa using marginBlocks_P4_d_e

lemma margin_P5Profile_a_b : margin P5Profile a b = (-80 : Int) := by
  calc
    margin P5Profile a b = marginBlocks blocksP5 a b := margin_P5Profile_eq_blocks (a := a) (b := b)
      (by decide)
    _ = (-80 : Int) := by simpa using marginBlocks_P5_a_b

lemma margin_P5Profile_a_c : margin P5Profile a c = 138 := by
  calc
    margin P5Profile a c = marginBlocks blocksP5 a c := margin_P5Profile_eq_blocks (a := a) (b := c)
      (by decide)
    _ = 138 := by simpa using marginBlocks_P5_a_c

lemma margin_P5Profile_a_d : margin P5Profile a d = 18 := by
  calc
    margin P5Profile a d = marginBlocks blocksP5 a d := margin_P5Profile_eq_blocks (a := a) (b := d)
      (by decide)
    _ = 18 := by simpa using marginBlocks_P5_a_d

lemma margin_P5Profile_a_e : margin P5Profile a e = 36 := by
  calc
    margin P5Profile a e = marginBlocks blocksP5 a e := margin_P5Profile_eq_blocks (a := a) (b := e)
      (by decide)
    _ = 36 := by simpa using marginBlocks_P5_a_e

lemma margin_P5Profile_b_c : margin P5Profile b c = 92 := by
  calc
    margin P5Profile b c = marginBlocks blocksP5 b c := margin_P5Profile_eq_blocks (a := b) (b := c)
      (by decide)
    _ = 92 := by simpa using marginBlocks_P5_b_c

lemma margin_P5Profile_b_d : margin P5Profile b d = 12 := by
  calc
    margin P5Profile b d = marginBlocks blocksP5 b d := margin_P5Profile_eq_blocks (a := b) (b := d)
      (by decide)
    _ = 12 := by simpa using marginBlocks_P5_b_d

lemma margin_P5Profile_b_e : margin P5Profile b e = (-42 : Int) := by
  calc
    margin P5Profile b e = marginBlocks blocksP5 b e := margin_P5Profile_eq_blocks (a := b) (b := e)
      (by decide)
    _ = (-42 : Int) := by simpa using marginBlocks_P5_b_e

lemma margin_P5Profile_c_d : margin P5Profile c d = 6 := by
  calc
    margin P5Profile c d = marginBlocks blocksP5 c d := margin_P5Profile_eq_blocks (a := c) (b := d)
      (by decide)
    _ = 6 := by simpa using marginBlocks_P5_c_d

lemma margin_P5Profile_c_e : margin P5Profile c e = 24 := by
  calc
    margin P5Profile c e = marginBlocks blocksP5 c e := margin_P5Profile_eq_blocks (a := c) (b := e)
      (by decide)
    _ = 24 := by simpa using marginBlocks_P5_c_e

lemma margin_P5Profile_d_e : margin P5Profile d e = 30 := by
  calc
    margin P5Profile d e = marginBlocks blocksP5 d e := margin_P5Profile_eq_blocks (a := d) (b := e)
      (by decide)
    _ = 30 := by simpa using marginBlocks_P5_d_e

lemma marginBlocks_P1_b_a : marginBlocks blocksP1 b a = 84 := by
  decide

lemma marginBlocks_P2_b_a : marginBlocks blocksP2 b a = 57 := by
  decide

lemma marginBlocks_P4_b_a : marginBlocks blocksP4 b a = 87 := by
  decide

lemma margin_P1Profile_b_a : margin P1Profile b a = 84 := by
  calc
    margin P1Profile b a = marginBlocks blocksP1 b a := margin_P1Profile_eq_blocks (a := b) (b := a)
      (by decide)
    _ = 84 := by simpa using marginBlocks_P1_b_a

lemma margin_P2Profile_b_a : margin P2Profile b a = 57 := by
  calc
    margin P2Profile b a = marginBlocks blocksP2 b a := margin_P2Profile_eq_blocks (a := b) (b := a)
      (by decide)
    _ = 57 := by simpa using marginBlocks_P2_b_a

lemma margin_P4Profile_b_a : margin P4Profile b a = 87 := by
  calc
    margin P4Profile b a = marginBlocks blocksP4 b a := margin_P4Profile_eq_blocks (a := b) (b := a)
      (by decide)
    _ = 87 := by simpa using marginBlocks_P4_b_a

end Holliday

end SocialChoice
