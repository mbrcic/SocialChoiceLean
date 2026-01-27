import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic
import SocialChoice.ListBallot
import SocialChoice.Margin
import SocialChoice.Profile

namespace SocialChoice

open Finset

/-!
Debord–McGarvey theorem: For any skew-symmetric margin function, such that all
margins are even or all margins are odd, there exists a profile that realises it.

We construct profiles from list-based ballots and block lists. The even-margin case
is handled by composing "edge" ballots (one pair gets ±2, others 0). The odd-margin
case reduces to the even one by shifting margins by ±1 depending on the ordering of
the pair, then adding a single identity ballot.
-/

section DebordMcGarvey

variable {n : ℕ}

noncomputable def edgeBallot (a b : Fin n) : ListBallot n := by
  classical
  by_cases h : a = b
  · exact ListBallot.identity n
  ·
    let others :=
      (List.finRange n).filter (fun c => decide (c ≠ a ∧ c ≠ b))
    have hnodup_others : others.Nodup := by
      simpa [others] using
        (List.Nodup.filter (p := fun c => decide (c ≠ a ∧ c ≠ b))
          (List.nodup_finRange n))
    have ha_not_mem : a ∉ others := by
      intro ha
      have h' : decide (a ≠ a ∧ a ≠ b) = true := (List.mem_filter.mp ha).2
      have h'' : a ≠ a ∧ a ≠ b := (decide_eq_true_eq.mp h')
      exact h''.1 rfl
    have hb_not_mem : b ∉ others := by
      intro hb
      have h' : decide (b ≠ a ∧ b ≠ b) = true := (List.mem_filter.mp hb).2
      have h'' : b ≠ a ∧ b ≠ b := (decide_eq_true_eq.mp h')
      exact h''.2 rfl
    have hnodup : (a :: b :: others).Nodup := by
      have hne : a ≠ b := h
      have ha_not_mem' : a ∉ b :: others := by
        simp [hne, ha_not_mem]
      have hb_not_mem' : b ∉ others := hb_not_mem
      apply List.nodup_cons.2
      refine ⟨ha_not_mem', ?_⟩
      apply List.nodup_cons.2
      exact ⟨hb_not_mem', hnodup_others⟩
    have hperm : (a :: b :: others).Perm (List.finRange n) := by
      refine (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).2 ?_
      intro c
      constructor
      · intro _hc
        exact List.mem_finRange c
      · intro _hc
        by_cases hca : c = a
        · simp [hca]
        by_cases hcb : c = b
        · simp [hcb]
        have hmem : c ∈ others := by
          apply List.mem_filter.mpr
          refine ⟨List.mem_finRange c, ?_⟩
          have : c ≠ a ∧ c ≠ b := ⟨hca, hcb⟩
          simp [this]
        simp [hca, hcb, hmem]
    exact ⟨a :: b :: others, hperm⟩

noncomputable def edgeBallotRev (a b : Fin n) : ListBallot n := by
  classical
  by_cases h : a = b
  · exact ListBallot.identity n
  ·
    let others :=
      (List.finRange n).filter (fun c => decide (c ≠ a ∧ c ≠ b))
    let revOthers := others.reverse
    have hnodup_others : others.Nodup := by
      simpa [others] using
        (List.Nodup.filter (p := fun c => decide (c ≠ a ∧ c ≠ b))
          (List.nodup_finRange n))
    have hnodup_rev : revOthers.Nodup := by
      simpa [revOthers] using (List.nodup_reverse.mpr hnodup_others)
    have ha_not_mem : a ∉ others := by
      intro ha
      have h' : decide (a ≠ a ∧ a ≠ b) = true := (List.mem_filter.mp ha).2
      have h'' : a ≠ a ∧ a ≠ b := (decide_eq_true_eq.mp h')
      exact h''.1 rfl
    have hb_not_mem : b ∉ others := by
      intro hb
      have h' : decide (b ≠ a ∧ b ≠ b) = true := (List.mem_filter.mp hb).2
      have h'' : b ≠ a ∧ b ≠ b := (decide_eq_true_eq.mp h')
      exact h''.2 rfl
    have ha_not_mem_rev : a ∉ revOthers := by
      simpa [revOthers] using ha_not_mem
    have hb_not_mem_rev : b ∉ revOthers := by
      simpa [revOthers] using hb_not_mem
    have hnodup_ab : ([a, b] : List (Fin n)).Nodup := by
      simp [h]
    have hdisj : List.Disjoint revOthers [a, b] := by
      refine List.disjoint_left.2 ?_
      intro x hx hy
      have hxab : x = a ∨ x = b := by
        simpa using hy
      cases hxab with
      | inl hxa =>
          exact (ha_not_mem_rev (by simpa [hxa] using hx)).elim
      | inr hxb =>
          exact (hb_not_mem_rev (by simpa [hxb] using hx)).elim
    have hnodup : (revOthers ++ [a, b]).Nodup := by
      exact (List.nodup_append'.2 ⟨hnodup_rev, hnodup_ab, hdisj⟩)
    have hperm : (revOthers ++ [a, b]).Perm (List.finRange n) := by
      refine (List.perm_ext_iff_of_nodup hnodup (List.nodup_finRange n)).2 ?_
      intro c
      constructor
      · intro _hc
        exact List.mem_finRange c
      · intro _hc
        by_cases hca : c = a
        · simp [hca]
        by_cases hcb : c = b
        · simp [hcb]
        have hmem : c ∈ others := by
          apply List.mem_filter.mpr
          refine ⟨List.mem_finRange c, ?_⟩
          have : c ≠ a ∧ c ≠ b := ⟨hca, hcb⟩
          simp [this]
        have hmem_rev : c ∈ revOthers := by
          simpa [revOthers] using (List.mem_reverse.mpr hmem)
        simp [hmem_rev, hca, hcb]
    exact ⟨revOthers ++ [a, b], hperm⟩

noncomputable def edgeBlocks (a b : Fin n) : List (Nat × ListBallot n) :=
  [(1, edgeBallot a b), (1, edgeBallotRev a b)]

lemma edgeBlocks_margin_ab {a b : Fin n} (hne : a ≠ b) :
    marginBlocks (edgeBlocks a b) a b = 2 := by
  classical
  have hpref1 : prefersInList (edgeBallot a b).ranking a b = true := by
    simp [edgeBallot, hne, prefersInList]
  have hpref2 : prefersInList (edgeBallotRev a b).ranking a b = true := by
    -- unfold edgeBallotRev and compute indices in the appended list
    by_cases h : a = b
    · exact (hne h).elim
    let others :=
      (List.finRange n).filter (fun c => decide (c ≠ a ∧ c ≠ b))
    let revOthers := others.reverse
    have ha_not_mem : a ∉ revOthers := by
      have ha_not_mem' : a ∉ others := by
        intro ha
        have h' : decide (a ≠ a ∧ a ≠ b) = true := (List.mem_filter.mp ha).2
        have h'' : a ≠ a ∧ a ≠ b := (decide_eq_true_eq.mp h')
        exact h''.1 rfl
      simpa [revOthers] using ha_not_mem'
    have hb_not_mem : b ∉ revOthers := by
      have hb_not_mem' : b ∉ others := by
        intro hb
        have h' : decide (b ≠ a ∧ b ≠ b) = true := (List.mem_filter.mp hb).2
        have h'' : b ≠ a ∧ b ≠ b := (decide_eq_true_eq.mp h')
        exact h''.2 rfl
      simpa [revOthers] using hb_not_mem'
    have hidx_a :
        (revOthers ++ [a, b]).idxOf a = revOthers.length + ([a, b].idxOf a) := by
      simpa using (List.idxOf_append_of_notMem (l₁ := revOthers) (l₂ := [a, b]) ha_not_mem)
    have hidx_b :
        (revOthers ++ [a, b]).idxOf b = revOthers.length + ([a, b].idxOf b) := by
      simpa using (List.idxOf_append_of_notMem (l₁ := revOthers) (l₂ := [a, b]) hb_not_mem)
    have hidx_a' : ([a, b].idxOf a) = 0 := by simp
    have hidx_b' : ([a, b].idxOf b) = 1 := by
      simp [h]
    have hlt :
        (revOthers ++ [a, b]).idxOf a < (revOthers ++ [a, b]).idxOf b := by
      simp [hidx_a, hidx_b, hidx_a', hidx_b']
    simpa [edgeBallotRev, h, prefersInList, revOthers, others] using hlt
  -- combine both ballots
  simp [edgeBlocks, marginBlocks, marginOfBallot, hpref1, hpref2]

private lemma idxOf_reverse_of_mem {α : Type} [DecidableEq α] {l : List α}
    (hnodup : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x = l.length - 1 - l.idxOf x := by
  induction l with
  | nil =>
      cases hx
  | cons a t ih =>
      have hnodup' : t.Nodup := (List.nodup_cons.mp hnodup).2
      have ha_not_mem : a ∉ t := (List.nodup_cons.mp hnodup).1
      by_cases hxa : x = a
      · subst hxa
        have hx_not_mem_rev : x ∉ t.reverse := by
          intro ha
          exact ha_not_mem (List.mem_reverse.mp ha)
        calc
          (x :: t).reverse.idxOf x = (t.reverse ++ [x]).idxOf x := by
            simp [List.reverse_cons]
          _ = t.reverse.length + ([x].idxOf x) := by
            simpa using
              (List.idxOf_append_of_notMem (l₁ := t.reverse) (l₂ := [x]) hx_not_mem_rev)
          _ = t.length := by simp
          _ = (x :: t).length - 1 - (x :: t).idxOf x := by simp
      ·
        have hx_t : x ∈ t := by
          rcases (List.mem_cons.mp hx) with hxa' | hx'
          · exact (hxa hxa').elim
          · exact hx'
        have hx_rev : x ∈ t.reverse := by
          simpa using (List.mem_reverse.mpr hx_t)
        have hidx_rev :
            (a :: t).reverse.idxOf x = t.reverse.idxOf x := by
          simp [List.reverse_cons, List.idxOf_append_of_mem, hx_rev]
        have hidx_cons :
            (a :: t).idxOf x = Nat.succ (t.idxOf x) := by
          have hax : a ≠ x := by simpa [ne_comm] using hxa
          simp [List.idxOf_cons_ne, hax]
        calc
          (a :: t).reverse.idxOf x = t.reverse.idxOf x := hidx_rev
          _ = t.length - 1 - t.idxOf x := ih hnodup' hx_t
          _ = (a :: t).length - 1 - (a :: t).idxOf x := by
                simp [hidx_cons, Nat.succ_eq_add_one, Nat.sub_sub, Nat.add_comm]

private lemma prefersInList_reverse_of_nodup {α : Type} [DecidableEq α]
    {l : List α} (hnodup : l.Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    prefersInList l.reverse x y = prefersInList l y x := by
  have hxlt : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  have hylt : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hy
  have hidx_x : l.reverse.idxOf x = l.length - 1 - l.idxOf x :=
    idxOf_reverse_of_mem hnodup hx
  have hidx_y : l.reverse.idxOf y = l.length - 1 - l.idxOf y :=
    idxOf_reverse_of_mem hnodup hy
  unfold prefersInList
  by_cases hlt : l.idxOf y < l.idxOf x
  · have hrev : l.length - 1 - l.idxOf x < l.length - 1 - l.idxOf y := by
      omega
    simp [hidx_x, hidx_y, hlt, hrev]
  · have hrev : ¬ l.length - 1 - l.idxOf x < l.length - 1 - l.idxOf y := by
      omega
    simp [hidx_x, hidx_y, hlt, hrev]

lemma edgeBlocks_margin_other {a b c d : Fin n} (hne : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    marginBlocks (edgeBlocks a b) c d = 0 := by
  classical
  let others := (List.finRange n).filter (fun x => decide (x ≠ a ∧ x ≠ b))
  let revOthers := others.reverse
  have hnodup_others : others.Nodup := by
    simpa [others] using
      (List.Nodup.filter (p := fun x => decide (x ≠ a ∧ x ≠ b)) (List.nodup_finRange n))
  have hc_mem : c ∈ others := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange c, ?_⟩
    have : c ≠ a ∧ c ≠ b := ⟨hca, hcb⟩
    simp [this]
  have hd_mem : d ∈ others := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange d, ?_⟩
    have : d ≠ a ∧ d ≠ b := ⟨hda, hdb⟩
    simp [this]
  have hc_mem_rev : c ∈ revOthers := by
    simpa [revOthers] using (List.mem_reverse.mpr hc_mem)
  have hd_mem_rev : d ∈ revOthers := by
    simpa [revOthers] using (List.mem_reverse.mpr hd_mem)
  have hca' : a ≠ c := by simpa [ne_comm] using hca
  have hcb' : b ≠ c := by simpa [ne_comm] using hcb
  have hda' : a ≠ d := by simpa [ne_comm] using hda
  have hdb' : b ≠ d := by simpa [ne_comm] using hdb
  have hpref_edge :
      prefersInList (edgeBallot a b).ranking c d = prefersInList others c d := by
    simp [edgeBallot, hne, prefersInList, others, List.idxOf_cons_ne, hca', hcb', hda', hdb']
  have hpref_rev :
      prefersInList (edgeBallotRev a b).ranking c d = prefersInList others d c := by
    have hidx_c :
        (revOthers ++ [a, b]).idxOf c = revOthers.idxOf c := by
      simpa using (List.idxOf_append_of_mem (l₁ := revOthers) (l₂ := [a, b]) hc_mem_rev)
    have hidx_d :
        (revOthers ++ [a, b]).idxOf d = revOthers.idxOf d := by
      simpa using (List.idxOf_append_of_mem (l₁ := revOthers) (l₂ := [a, b]) hd_mem_rev)
    have hpref_rev' :
        prefersInList (revOthers ++ [a, b]) c d = prefersInList revOthers c d := by
      simp [prefersInList, hidx_c, hidx_d]
    have hrev :
        prefersInList revOthers c d = prefersInList others d c := by
      simpa [revOthers] using
        (prefersInList_reverse_of_nodup (l := others) hnodup_others hc_mem hd_mem)
    simpa [edgeBallotRev, hne, revOthers, others] using (hpref_rev'.trans hrev)
  have hne_idx : others.idxOf c ≠ others.idxOf d := by
    intro hidx
    have hcd' :=
      (List.idxOf_inj (l := others) (x := c) (y := d) hc_mem).mp hidx
    exact hcd hcd'
  cases hcd_pref : prefersInList others c d with
  | true =>
      have hlt : others.idxOf c < others.idxOf d := by
        simpa [prefersInList, decide_eq_true_eq] using hcd_pref
      have hdc_false : prefersInList others d c = false := by
        have hlt' : ¬ others.idxOf d < others.idxOf c := by
          exact lt_asymm hlt
        simp [prefersInList, hlt']
      simp [edgeBlocks, marginBlocks, marginOfBallot, hpref_edge, hpref_rev,
        hcd_pref, hdc_false]
  | false =>
      have hnot : ¬ others.idxOf c < others.idxOf d := by
        simpa [prefersInList, decide_eq_false_iff_not] using hcd_pref
      have hgt : others.idxOf d < others.idxOf c := by
        cases lt_or_gt_of_ne hne_idx with
        | inl hlt => exact (hnot hlt).elim
        | inr hgt => exact hgt
      have hdc_true : prefersInList others d c = true := by
        simpa [prefersInList, decide_eq_true_eq] using hgt
      simp [edgeBlocks, marginBlocks, marginOfBallot, hpref_edge, hpref_rev,
        hcd_pref, hdc_true]

lemma marginBlocks_skew {n : ℕ} (blocks : List (Nat × ListBallot n)) {a b : Fin n}
    (hne : a ≠ b) :
    marginBlocks blocks a b = - marginBlocks blocks b a := by
  have hprof :
      margin (profileOfBlocks blocks) a b = marginBlocks blocks a b :=
    margin_profileOfBlocks (blocks := blocks) (a := a) (b := b) hne
  have hprof' :
      margin (profileOfBlocks blocks) b a = marginBlocks blocks b a :=
    margin_profileOfBlocks (blocks := blocks) (a := b) (b := a) (by simpa [ne_comm] using hne)
  have hskew :=
    margin_antisymmetric (P := profileOfBlocks blocks) a b
  simpa [hprof, hprof'] using hskew

lemma edgeBlocks_margin_left_other {a b c : Fin n} (hne : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    marginBlocks (edgeBlocks a b) a c = 0 := by
  classical
  let others := (List.finRange n).filter (fun x => decide (x ≠ a ∧ x ≠ b))
  let revOthers := others.reverse
  have hc_mem : c ∈ others := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange c, ?_⟩
    have : c ≠ a ∧ c ≠ b := ⟨hca, hcb⟩
    simp [this]
  have hc_mem_rev : c ∈ revOthers := by
    simpa [revOthers] using (List.mem_reverse.mpr hc_mem)
  have ha_not_mem : a ∉ revOthers := by
    have ha_not_mem' : a ∉ others := by
      intro ha
      have h' : decide (a ≠ a ∧ a ≠ b) = true := (List.mem_filter.mp ha).2
      have h'' : a ≠ a ∧ a ≠ b := (decide_eq_true_eq.mp h')
      exact h''.1 rfl
    simpa [revOthers] using ha_not_mem'
  have hpref_edge : prefersInList (edgeBallot a b).ranking a c = true := by
    have hidx_c : (a :: b :: others).idxOf c = Nat.succ (Nat.succ (others.idxOf c)) := by
      calc
        (a :: b :: others).idxOf c = Nat.succ ((b :: others).idxOf c) := by
          simpa using
            (List.idxOf_cons_ne (l := b :: others) (a := c) (b := a)
              (by simpa [ne_comm] using hca))
        _ = Nat.succ (Nat.succ (others.idxOf c)) := by
          simp [List.idxOf_cons_ne, (by simpa [ne_comm] using hcb)]
    have hlt : (a :: b :: others).idxOf a < (a :: b :: others).idxOf c := by
      simp [hidx_c]
    have hidx : prefersInList (a :: b :: others) a c = true := by
      simpa [prefersInList] using hlt
    simpa [edgeBallot, hne, others] using hidx
  have hpref_rev_ca : prefersInList (edgeBallotRev a b).ranking c a = true := by
    have hidx_c :
        (revOthers ++ [a, b]).idxOf c = revOthers.idxOf c := by
      simpa using (List.idxOf_append_of_mem (l₁ := revOthers) (l₂ := [a, b]) hc_mem_rev)
    have hidx_a :
        (revOthers ++ [a, b]).idxOf a = revOthers.length + ([a, b].idxOf a) := by
      simpa using (List.idxOf_append_of_notMem (l₁ := revOthers) (l₂ := [a, b]) ha_not_mem)
    have hc_lt : revOthers.idxOf c < revOthers.length :=
      List.idxOf_lt_length_of_mem hc_mem_rev
    have hlt :
        (revOthers ++ [a, b]).idxOf c < (revOthers ++ [a, b]).idxOf a := by
      simpa [hidx_c, hidx_a] using hc_lt
    simpa [edgeBallotRev, hne, prefersInList, revOthers, others, hidx_c, hidx_a] using hlt
  have hpref_rev : prefersInList (edgeBallotRev a b).ranking a c = false := by
    simpa using
      (prefersInList_asymm (b := edgeBallotRev a b) (a := c) (c := a) hpref_rev_ca)
  simp [edgeBlocks, marginBlocks, marginOfBallot, hpref_edge, hpref_rev]

lemma edgeBlocks_margin_right_other {a b c : Fin n} (hne : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    marginBlocks (edgeBlocks a b) b c = 0 := by
  classical
  let others := (List.finRange n).filter (fun x => decide (x ≠ a ∧ x ≠ b))
  let revOthers := others.reverse
  have hc_mem : c ∈ others := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange c, ?_⟩
    have : c ≠ a ∧ c ≠ b := ⟨hca, hcb⟩
    simp [this]
  have hc_mem_rev : c ∈ revOthers := by
    simpa [revOthers] using (List.mem_reverse.mpr hc_mem)
  have hb_not_mem : b ∉ revOthers := by
    have hb_not_mem' : b ∉ others := by
      intro hb
      have h' : decide (b ≠ a ∧ b ≠ b) = true := (List.mem_filter.mp hb).2
      have h'' : b ≠ a ∧ b ≠ b := (decide_eq_true_eq.mp h')
      exact h''.2 rfl
    simpa [revOthers] using hb_not_mem'
  have hpref_edge : prefersInList (edgeBallot a b).ranking b c = true := by
    have hba : b ≠ a := by simpa [ne_comm] using hne
    have hidx_b : (a :: b :: others).idxOf b = 1 := by
      calc
        (a :: b :: others).idxOf b = Nat.succ ((b :: others).idxOf b) := by
          simpa using
            (List.idxOf_cons_ne (l := b :: others) (a := b) (b := a)
              (by simpa [ne_comm] using hba))
        _ = 1 := by simp
    have hidx_c : (a :: b :: others).idxOf c = Nat.succ (Nat.succ (others.idxOf c)) := by
      calc
        (a :: b :: others).idxOf c = Nat.succ ((b :: others).idxOf c) := by
          simpa using
            (List.idxOf_cons_ne (l := b :: others) (a := c) (b := a)
              (by simpa [ne_comm] using hca))
        _ = Nat.succ (Nat.succ (others.idxOf c)) := by
          simp [List.idxOf_cons_ne, (by simpa [ne_comm] using hcb)]
    have hlt : (a :: b :: others).idxOf b < (a :: b :: others).idxOf c := by
      simp [hidx_b, hidx_c]
    have hidx : prefersInList (a :: b :: others) b c = true := by
      simpa [prefersInList] using hlt
    simpa [edgeBallot, hne, others] using hidx
  have hpref_rev_cb : prefersInList (edgeBallotRev a b).ranking c b = true := by
    have hidx_c :
        (revOthers ++ [a, b]).idxOf c = revOthers.idxOf c := by
      simpa using (List.idxOf_append_of_mem (l₁ := revOthers) (l₂ := [a, b]) hc_mem_rev)
    have hidx_b :
        (revOthers ++ [a, b]).idxOf b = revOthers.length + ([a, b].idxOf b) := by
      simpa using (List.idxOf_append_of_notMem (l₁ := revOthers) (l₂ := [a, b]) hb_not_mem)
    have hc_lt : revOthers.idxOf c < revOthers.length :=
      List.idxOf_lt_length_of_mem hc_mem_rev
    have hidx_b' : ([a, b].idxOf b) = 1 := by
      simp [hne]
    have hlt :
        (revOthers ++ [a, b]).idxOf c < (revOthers ++ [a, b]).idxOf b := by
      have hlt' : revOthers.idxOf c < revOthers.length + 1 := by
        simpa using (Nat.lt_succ_of_lt hc_lt)
      simpa [hidx_c, hidx_b, hidx_b'] using hlt'
    simpa [edgeBallotRev, hne, prefersInList, revOthers, others, hidx_c, hidx_b] using hlt
  have hpref_rev : prefersInList (edgeBallotRev a b).ranking b c = false := by
    simpa using
      (prefersInList_asymm (b := edgeBallotRev a b) (a := c) (c := b) hpref_rev_cb)
  simp [edgeBlocks, marginBlocks, marginOfBallot, hpref_edge, hpref_rev]

lemma marginBlocks_append {n : ℕ} (xs ys : List (Nat × ListBallot n)) (a b : Fin n) :
    marginBlocks (xs ++ ys) a b = marginBlocks xs a b + marginBlocks ys a b := by
  induction xs with
  | nil =>
      simp [marginBlocks]
  | cons head tail ih =>
      cases head with
      | mk k ballot =>
          simp [marginBlocks_cons, ih, add_assoc]

noncomputable def edgeBlocksOfInt (a b : Fin n) (k : Int) : List (Nat × ListBallot n) := by
  classical
  let z : Int := k / 2
  by_cases hz : 0 ≤ z
  ·
    let m : Nat := Int.toNat z
    exact [(m, edgeBallot a b), (m, edgeBallotRev a b)]
  ·
    let m : Nat := Int.toNat (-z)
    exact [(m, edgeBallot b a), (m, edgeBallotRev b a)]

private lemma edgeBlocksNat_margin_ab {a b : Fin n} (hne : a ≠ b) (m : Nat) :
    marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a b = (m : Int) * 2 := by
  have hscale :
      marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a b =
        (m : Int) * marginBlocks (edgeBlocks a b) a b := by
    have h1 :
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a b =
          (m : Int) * marginOfBallot (edgeBallot a b) a b +
            (m : Int) * marginOfBallot (edgeBallotRev a b) a b := by
      simp [marginBlocks]
    have h2 :
        marginBlocks (edgeBlocks a b) a b =
          marginOfBallot (edgeBallot a b) a b +
            marginOfBallot (edgeBallotRev a b) a b := by
      simp [edgeBlocks, marginBlocks]
    calc
      marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a b =
          (m : Int) * marginOfBallot (edgeBallot a b) a b +
            (m : Int) * marginOfBallot (edgeBallotRev a b) a b := h1
      _ = (m : Int) *
            (marginOfBallot (edgeBallot a b) a b +
              marginOfBallot (edgeBallotRev a b) a b) := by ring
      _ = (m : Int) * marginBlocks (edgeBlocks a b) a b := by
            simp [h2]
  simpa [edgeBlocks_margin_ab hne] using hscale

lemma edgeBlocksOfInt_margin_ab {a b : Fin n} (hne : a ≠ b) (k : Int)
    (heven : Even k) :
    marginBlocks (edgeBlocksOfInt a b k) a b = k := by
  classical
  unfold edgeBlocksOfInt
  set z : Int := k / 2
  have hk : k = 2 * z := by
    simpa [z, Int.mul_ediv_cancel_left, two_mul] using (Int.two_mul_ediv_two_of_even heven).symm
  by_cases hz : 0 ≤ z
  ·
    let m : Nat := Int.toNat z
    have hm : (m : Int) = z := by
      simpa [m] using (Int.toNat_of_nonneg hz)
    have hcalc : marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a b = (m : Int) * 2 :=
      edgeBlocksNat_margin_ab (a := a) (b := b) hne m
    simpa [hz, m, hm, hk, mul_comm, mul_left_comm, mul_assoc] using hcalc
  ·
    have hz' : 0 ≤ -z := by
      exact neg_nonneg.mpr (le_of_not_ge hz)
    let m : Nat := Int.toNat (-z)
    have hm : (m : Int) = -z := by
      simpa [m] using (Int.toNat_of_nonneg hz')
    have hne' : b ≠ a := by
      exact Ne.symm hne
    have hcalc : marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] b a = (m : Int) * 2 :=
      edgeBlocksNat_margin_ab (a := b) (b := a) hne' m
    have hskew :
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] a b =
          - marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] b a := by
      have hprof :
          margin (profileOfBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)]) a b =
            marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] a b :=
        margin_profileOfBlocks (blocks := [(m, edgeBallot b a), (m, edgeBallotRev b a)]) (a := a) (b := b) hne
      have hprof' :
          margin (profileOfBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)]) b a =
            marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] b a :=
        margin_profileOfBlocks (blocks := [(m, edgeBallot b a), (m, edgeBallotRev b a)]) (a := b) (b := a) hne'
      have hskewP :=
        margin_antisymmetric (P := profileOfBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)]) a b
      -- `hskewP` gives `margin ... a b = - margin ... b a`
      simpa [hprof, hprof'] using hskewP
    have hcalc' :
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] a b = -((m : Int) * 2) := by
      simpa [hcalc] using hskew
    have hk' : k = - (2 * (-z)) := by
      have : 2 * (-z) = - (2 * z) := by ring
      calc
        k = 2 * z := hk
        _ = - (2 * (-z)) := by
              have h' : 2 * (-z) = - (2 * z) := by ring
              nlinarith
    -- finish
    simpa [hz, m, hm, hk, mul_comm, mul_left_comm, mul_assoc] using hcalc'

lemma edgeBlocksOfInt_margin_other {a b c d : Fin n} (hne : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) (k : Int) :
    marginBlocks (edgeBlocksOfInt a b k) c d = 0 := by
  classical
  unfold edgeBlocksOfInt
  set z : Int := k / 2
  by_cases hz : 0 ≤ z
  ·
    let m : Nat := Int.toNat z
    have hscale :
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] c d =
          (m : Int) * marginBlocks (edgeBlocks a b) c d := by
      have h1 :
          marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] c d =
            (m : Int) * marginOfBallot (edgeBallot a b) c d +
              (m : Int) * marginOfBallot (edgeBallotRev a b) c d := by
        simp [marginBlocks]
      have h2 :
          marginBlocks (edgeBlocks a b) c d =
            marginOfBallot (edgeBallot a b) c d +
              marginOfBallot (edgeBallotRev a b) c d := by
        simp [edgeBlocks, marginBlocks]
      calc
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] c d =
            (m : Int) * marginOfBallot (edgeBallot a b) c d +
              (m : Int) * marginOfBallot (edgeBallotRev a b) c d := h1
        _ = (m : Int) *
              (marginOfBallot (edgeBallot a b) c d +
                marginOfBallot (edgeBallotRev a b) c d) := by ring
        _ = (m : Int) * marginBlocks (edgeBlocks a b) c d := by
              simp [h2]
    have hzero :
        marginBlocks (edgeBlocks a b) c d = 0 :=
      edgeBlocks_margin_other (a := a) (b := b) (c := c) (d := d)
        hne hca hcb hda hdb hcd
    simpa [hz, m, hzero] using hscale
  ·
    let m : Nat := Int.toNat (-z)
    have hne' : b ≠ a := by exact Ne.symm hne
    have hca' : c ≠ b := by exact hcb
    have hcb' : c ≠ a := by exact hca
    have hda' : d ≠ b := by exact hdb
    have hdb' : d ≠ a := by exact hda
    have hzero :
        marginBlocks (edgeBlocks b a) c d = 0 :=
      edgeBlocks_margin_other (a := b) (b := a) (c := c) (d := d)
        hne' hca' hcb' hda' hdb' hcd
    have hscale :
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] c d =
          (m : Int) * marginBlocks (edgeBlocks b a) c d := by
      have h1 :
          marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] c d =
            (m : Int) * marginOfBallot (edgeBallot b a) c d +
              (m : Int) * marginOfBallot (edgeBallotRev b a) c d := by
        simp [marginBlocks]
      have h2 :
          marginBlocks (edgeBlocks b a) c d =
            marginOfBallot (edgeBallot b a) c d +
              marginOfBallot (edgeBallotRev b a) c d := by
        simp [edgeBlocks, marginBlocks]
      calc
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] c d =
            (m : Int) * marginOfBallot (edgeBallot b a) c d +
              (m : Int) * marginOfBallot (edgeBallotRev b a) c d := h1
        _ = (m : Int) *
              (marginOfBallot (edgeBallot b a) c d +
                marginOfBallot (edgeBallotRev b a) c d) := by ring
        _ = (m : Int) * marginBlocks (edgeBlocks b a) c d := by
              simp [h2]
    simpa [hz, m, hzero] using hscale

lemma edgeBlocksOfInt_margin_left_other {a b c : Fin n} (hne : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (k : Int) :
    marginBlocks (edgeBlocksOfInt a b k) a c = 0 := by
  classical
  unfold edgeBlocksOfInt
  set z : Int := k / 2
  by_cases hz : 0 ≤ z
  ·
    let m : Nat := Int.toNat z
    have hscale :
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a c =
          (m : Int) * marginBlocks (edgeBlocks a b) a c := by
      have h1 :
          marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a c =
            (m : Int) * marginOfBallot (edgeBallot a b) a c +
              (m : Int) * marginOfBallot (edgeBallotRev a b) a c := by
        simp [marginBlocks]
      have h2 :
          marginBlocks (edgeBlocks a b) a c =
            marginOfBallot (edgeBallot a b) a c +
              marginOfBallot (edgeBallotRev a b) a c := by
        simp [edgeBlocks, marginBlocks]
      calc
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] a c =
            (m : Int) * marginOfBallot (edgeBallot a b) a c +
              (m : Int) * marginOfBallot (edgeBallotRev a b) a c := h1
        _ = (m : Int) *
              (marginOfBallot (edgeBallot a b) a c +
                marginOfBallot (edgeBallotRev a b) a c) := by ring
        _ = (m : Int) * marginBlocks (edgeBlocks a b) a c := by
              simp [h2]
    have hzero :
        marginBlocks (edgeBlocks a b) a c = 0 :=
      edgeBlocks_margin_left_other (a := a) (b := b) (c := c) hne hca hcb
    simpa [hz, m, hzero] using hscale
  ·
    let m : Nat := Int.toNat (-z)
    have hne' : b ≠ a := by exact Ne.symm hne
    have hca' : c ≠ b := by exact hcb
    have hcb' : c ≠ a := by exact hca
    have hzero :
        marginBlocks (edgeBlocks b a) a c = 0 :=
      edgeBlocks_margin_right_other (a := b) (b := a) (c := c) hne' hca' hcb'
    have hscale :
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] a c =
          (m : Int) * marginBlocks (edgeBlocks b a) a c := by
      have h1 :
          marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] a c =
            (m : Int) * marginOfBallot (edgeBallot b a) a c +
              (m : Int) * marginOfBallot (edgeBallotRev b a) a c := by
        simp [marginBlocks]
      have h2 :
          marginBlocks (edgeBlocks b a) a c =
            marginOfBallot (edgeBallot b a) a c +
              marginOfBallot (edgeBallotRev b a) a c := by
        simp [edgeBlocks, marginBlocks]
      calc
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] a c =
            (m : Int) * marginOfBallot (edgeBallot b a) a c +
              (m : Int) * marginOfBallot (edgeBallotRev b a) a c := h1
        _ = (m : Int) *
              (marginOfBallot (edgeBallot b a) a c +
                marginOfBallot (edgeBallotRev b a) a c) := by ring
        _ = (m : Int) * marginBlocks (edgeBlocks b a) a c := by
              simp [h2]
    simpa [hz, m, hzero] using hscale

lemma edgeBlocksOfInt_margin_right_other {a b c : Fin n} (hne : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (k : Int) :
    marginBlocks (edgeBlocksOfInt a b k) b c = 0 := by
  classical
  unfold edgeBlocksOfInt
  set z : Int := k / 2
  by_cases hz : 0 ≤ z
  ·
    let m : Nat := Int.toNat z
    have hscale :
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] b c =
          (m : Int) * marginBlocks (edgeBlocks a b) b c := by
      have h1 :
          marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] b c =
            (m : Int) * marginOfBallot (edgeBallot a b) b c +
              (m : Int) * marginOfBallot (edgeBallotRev a b) b c := by
        simp [marginBlocks]
      have h2 :
          marginBlocks (edgeBlocks a b) b c =
            marginOfBallot (edgeBallot a b) b c +
              marginOfBallot (edgeBallotRev a b) b c := by
        simp [edgeBlocks, marginBlocks]
      calc
        marginBlocks [(m, edgeBallot a b), (m, edgeBallotRev a b)] b c =
            (m : Int) * marginOfBallot (edgeBallot a b) b c +
              (m : Int) * marginOfBallot (edgeBallotRev a b) b c := h1
        _ = (m : Int) *
              (marginOfBallot (edgeBallot a b) b c +
                marginOfBallot (edgeBallotRev a b) b c) := by ring
        _ = (m : Int) * marginBlocks (edgeBlocks a b) b c := by
              simp [h2]
    have hzero :
        marginBlocks (edgeBlocks a b) b c = 0 :=
      edgeBlocks_margin_right_other (a := a) (b := b) (c := c) hne hca hcb
    simpa [hz, m, hzero] using hscale
  ·
    let m : Nat := Int.toNat (-z)
    have hne' : b ≠ a := by exact Ne.symm hne
    have hca' : c ≠ b := by exact hcb
    have hcb' : c ≠ a := by exact hca
    have hzero :
        marginBlocks (edgeBlocks b a) b c = 0 :=
      edgeBlocks_margin_left_other (a := b) (b := a) (c := c) hne' hca' hcb'
    have hscale :
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] b c =
          (m : Int) * marginBlocks (edgeBlocks b a) b c := by
      have h1 :
          marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] b c =
            (m : Int) * marginOfBallot (edgeBallot b a) b c +
              (m : Int) * marginOfBallot (edgeBallotRev b a) b c := by
        simp [marginBlocks]
      have h2 :
          marginBlocks (edgeBlocks b a) b c =
            marginOfBallot (edgeBallot b a) b c +
              marginOfBallot (edgeBallotRev b a) b c := by
        simp [edgeBlocks, marginBlocks]
      calc
        marginBlocks [(m, edgeBallot b a), (m, edgeBallotRev b a)] b c =
            (m : Int) * marginOfBallot (edgeBallot b a) b c +
              (m : Int) * marginOfBallot (edgeBallotRev b a) b c := h1
        _ = (m : Int) *
              (marginOfBallot (edgeBallot b a) b c +
                marginOfBallot (edgeBallotRev b a) b c) := by ring
        _ = (m : Int) * marginBlocks (edgeBlocks b a) b c := by
              simp [h2]
    simpa [hz, m, hzero] using hscale

private lemma foldr_add_eq_zero_of_forall {α : Type} (f : α → Int) {l : List α}
    (hzero : ∀ x ∈ l, f x = 0) :
    l.foldr (fun x acc => f x + acc) 0 = 0 := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x = 0 := hzero x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := by
        intro y hy
        exact hzero y (by simp [hy])
      simp [List.foldr, hx, ih hxs]

private lemma foldr_add_eq_of_mem {α : Type} [DecidableEq α] (f : α → Int) {l : List α} {x : α}
    (hnd : l.Nodup) (hmem : x ∈ l) (hzero : ∀ y ∈ l, y ≠ x → f y = 0) :
    l.foldr (fun y acc => f y + acc) 0 = f x := by
  induction l with
  | nil =>
      cases hmem
  | cons y ys ih =>
      have hnd' : ys.Nodup := (List.nodup_cons.mp hnd).2
      rcases List.mem_cons.1 hmem with hmem | hmem
      · subst hmem
        have hzero' : ∀ y ∈ ys, f y = 0 := by
          intro y hy
          have hne : y ≠ x := by
            intro hxy
            subst hxy
            exact (List.nodup_cons.mp hnd).1 hy
          have : y ∈ (x :: ys) := by simp [hy]
          exact hzero y this hne
        have htail : ys.foldr (fun y acc => f y + acc) 0 = 0 :=
          foldr_add_eq_zero_of_forall f hzero'
        simp [List.foldr, htail]
      ·
        have hy' : y ≠ x := by
          intro hxy
          subst hxy
          exact (List.nodup_cons.mp hnd).1 hmem
        have hyzero : f y = 0 := hzero y (by simp) hy'
        have hzero_tail : ∀ z ∈ ys, z ≠ x → f z = 0 := by
          intro z hz hzx
          exact hzero z (by simp [hz]) hzx
        have htail : ys.foldr (fun y acc => f y + acc) 0 = f x :=
          ih hnd' hmem hzero_tail
        simp [List.foldr, hyzero, htail]

private lemma marginBlocks_foldr_pairs {n : ℕ} (pairs : List (Fin n × Fin n))
    (M : Fin n → Fin n → Int) (a b : Fin n) :
    marginBlocks
        (pairs.foldr (fun p acc => edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++ acc) []) a b =
      pairs.foldr
        (fun p acc => marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b + acc) 0 := by
  induction pairs with
  | nil =>
      simp [marginBlocks]
  | cons p ps ih =>
      calc
        marginBlocks
            (edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++
              ps.foldr (fun p acc => edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++ acc) []) a b =
            marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b +
              marginBlocks
                (ps.foldr (fun p acc => edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++ acc) []) a b := by
          simpa using
            (marginBlocks_append
              (xs := edgeBlocksOfInt p.1 p.2 (M p.1 p.2))
              (ys := ps.foldr (fun p acc => edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++ acc) [])
              (a := a) (b := b))
        _ = marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b +
              ps.foldr
                (fun p acc =>
                  marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b + acc) 0 := by
          rw [ih]
        _ = (p :: ps).foldr
              (fun p acc => marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b + acc) 0 := by
          simp [List.foldr]

noncomputable def blocksForMargins (M : Fin n → Fin n → Int) : List (Nat × ListBallot n) := by
  classical
  let pairs :=
    ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)).toList
  exact pairs.foldr (fun p acc => edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++ acc) []

lemma blocksForMargins_margin {M : Fin n → Fin n → Int} (hskew : skew_symmetric M)
    (heven : ∀ a b, Even (M a b)) {a b : Fin n} (hne : a ≠ b) :
    marginBlocks (blocksForMargins (n := n) M) a b = M a b := by
  classical
  let pairs :=
    ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)).toList
  have hdef :
      blocksForMargins (n := n) M =
        pairs.foldr (fun p acc => edgeBlocksOfInt p.1 p.2 (M p.1 p.2) ++ acc) [] := by
    simp [blocksForMargins, pairs]
  have hsum :
      marginBlocks (blocksForMargins (n := n) M) a b =
        pairs.foldr
          (fun p acc => marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b + acc) 0 := by
    simpa [hdef] using
      (marginBlocks_foldr_pairs (pairs := pairs) (M := M) (a := a) (b := b))
  let f : (Fin n × Fin n) → Int :=
    fun p => marginBlocks (edgeBlocksOfInt p.1 p.2 (M p.1 p.2)) a b
  have hnodup : pairs.Nodup := by
    simpa [pairs] using
      (Finset.nodup_toList
        ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)))
  by_cases hlt : a < b
  ·
    have hp0_mem : (a, b) ∈ pairs := by
      have :
          (a, b) ∈
            ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)) := by
        simp [Finset.mem_filter, hlt]
      simpa [pairs] using (Finset.mem_toList).2 this
    have hzero : ∀ p ∈ pairs, p ≠ (a, b) → f p = 0 := by
      intro p hp hnep
      rcases p with ⟨x, y⟩
      have hp' :
          (x, y) ∈
            ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)) := by
        simpa [pairs] using (Finset.mem_toList).1 hp
      have hxy : x < y := (Finset.mem_filter.mp hp').2
      have hxy_ne : x ≠ y := ne_of_lt hxy
      by_cases hxa : x = a
      · subst hxa
        by_cases hyb : y = b
        · subst hyb
          exact (hnep rfl).elim
        ·
          have hca : b ≠ x := Ne.symm hne
          have hcb : b ≠ y := by simpa [ne_comm] using hyb
          simpa [f] using
            (edgeBlocksOfInt_margin_left_other (a := x) (b := y) (c := b)
              (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
      ·
        by_cases hya : y = a
        · subst hya
          have hca : b ≠ x := by
            intro hbx
            subst hbx
            exact (lt_asymm hlt (by simpa using hxy))
          have hcb : b ≠ y := by exact Ne.symm hne
          simpa [f] using
            (edgeBlocksOfInt_margin_right_other (a := x) (b := y) (c := b)
              (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
        ·
          by_cases hxb : x = b
          · subst hxb
            have hca : a ≠ x := hne
            have hcb : a ≠ y := by simpa [ne_comm] using hya
            have hzero' :
                marginBlocks (edgeBlocksOfInt x y (M x y)) x a = 0 := by
              simpa using
                (edgeBlocksOfInt_margin_left_other (a := x) (b := y) (c := a)
                  (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
            have hskew' :
                marginBlocks (edgeBlocksOfInt x y (M x y)) a x =
                  - marginBlocks (edgeBlocksOfInt x y (M x y)) x a :=
              marginBlocks_skew (blocks := edgeBlocksOfInt x y (M x y)) (a := a) (b := x) hca
            have hzero : marginBlocks (edgeBlocksOfInt x y (M x y)) a x = 0 := by
              simpa [hzero'] using hskew'
            simpa [f] using hzero
          ·
            by_cases hyb : y = b
            · subst hyb
              have hca : a ≠ x := by simpa [ne_comm] using hxa
              have hcb : a ≠ y := by simpa using hne
              have hzero' :
                  marginBlocks (edgeBlocksOfInt x y (M x y)) y a = 0 := by
                simpa using
                  (edgeBlocksOfInt_margin_right_other (a := x) (b := y) (c := a)
                    (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
              have hskew' :
                  marginBlocks (edgeBlocksOfInt x y (M x y)) a y =
                    - marginBlocks (edgeBlocksOfInt x y (M x y)) y a :=
                marginBlocks_skew (blocks := edgeBlocksOfInt x y (M x y)) (a := a) (b := y) hcb
              have hzero : marginBlocks (edgeBlocksOfInt x y (M x y)) a y = 0 := by
                simpa [hzero'] using hskew'
              simpa [f] using hzero
            ·
              have hca : a ≠ x := by simpa [ne_comm] using hxa
              have hcb : a ≠ y := by simpa [ne_comm] using hya
              have hda : b ≠ x := by simpa [ne_comm] using hxb
              have hdb : b ≠ y := by simpa [ne_comm] using hyb
              simpa [f] using
                (edgeBlocksOfInt_margin_other (a := x) (b := y) (c := a) (d := b)
                  (hne := hxy_ne) (hca := hca) (hcb := hcb)
                  (hda := hda) (hdb := hdb) (hcd := hne) (k := M x y))
    have hf0 : f (a, b) = M a b := by
      simpa [f] using
        (edgeBlocksOfInt_margin_ab (a := a) (b := b) hne (k := M a b) (heven := heven a b))
    have hsum' :
        pairs.foldr (fun p acc => f p + acc) 0 = f (a, b) :=
      foldr_add_eq_of_mem f hnodup hp0_mem hzero
    simpa [hsum, hf0, f] using hsum'
  ·
    have hgt : b < a := by
      cases lt_or_gt_of_ne hne with
      | inl hlt' => exact (hlt hlt').elim
      | inr hgt' => exact hgt'
    have hp0_mem : (b, a) ∈ pairs := by
      have :
          (b, a) ∈
            ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)) := by
        simp [Finset.mem_filter, hgt]
      simpa [pairs] using (Finset.mem_toList).2 this
    have hzero : ∀ p ∈ pairs, p ≠ (b, a) → f p = 0 := by
      intro p hp hnep
      rcases p with ⟨x, y⟩
      have hp' :
          (x, y) ∈
            ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter (fun p => p.1 < p.2)) := by
        simpa [pairs] using (Finset.mem_toList).1 hp
      have hxy : x < y := (Finset.mem_filter.mp hp').2
      have hxy_ne : x ≠ y := ne_of_lt hxy
      by_cases hxb : x = b
      · subst hxb
        by_cases hya : y = a
        · subst hya
          exact (hnep rfl).elim
        ·
          have hca : a ≠ x := hne
          have hcb : a ≠ y := by simpa [ne_comm] using hya
          have hzero' :
              marginBlocks (edgeBlocksOfInt x y (M x y)) x a = 0 := by
            simpa using
              (edgeBlocksOfInt_margin_left_other (a := x) (b := y) (c := a)
                (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
          have hskew' :
              marginBlocks (edgeBlocksOfInt x y (M x y)) a x =
                - marginBlocks (edgeBlocksOfInt x y (M x y)) x a :=
            marginBlocks_skew (blocks := edgeBlocksOfInt x y (M x y)) (a := a) (b := x) hca
          have hzero : marginBlocks (edgeBlocksOfInt x y (M x y)) a x = 0 := by
            simpa [hzero'] using hskew'
          simpa [f] using hzero
      ·
        by_cases hya : y = b
        · subst hya
          have hca : a ≠ x := by
            intro hax
            subst hax
            exact (lt_asymm hgt (by simpa using hxy))
          have hcb : a ≠ y := by simpa using hne
          have hzero' :
              marginBlocks (edgeBlocksOfInt x y (M x y)) y a = 0 := by
            simpa using
              (edgeBlocksOfInt_margin_right_other (a := x) (b := y) (c := a)
                (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
          have hskew' :
              marginBlocks (edgeBlocksOfInt x y (M x y)) a y =
                - marginBlocks (edgeBlocksOfInt x y (M x y)) y a :=
            marginBlocks_skew (blocks := edgeBlocksOfInt x y (M x y)) (a := a) (b := y) hcb
          have hzero : marginBlocks (edgeBlocksOfInt x y (M x y)) a y = 0 := by
            simpa [hzero'] using hskew'
          simpa [f] using hzero
        ·
          by_cases hxa : x = a
          · subst hxa
            have hca : b ≠ x := Ne.symm hne
            have hcb : b ≠ y := by simpa [ne_comm] using hya
            simpa [f] using
              (edgeBlocksOfInt_margin_left_other (a := x) (b := y) (c := b)
                (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
          ·
            by_cases hyb : y = a
            · subst hyb
              have hca : b ≠ x := by simpa [ne_comm] using hxb
              have hcb : b ≠ y := Ne.symm hne
              simpa [f] using
                (edgeBlocksOfInt_margin_right_other (a := x) (b := y) (c := b)
                  (hne := hxy_ne) (hca := hca) (hcb := hcb) (k := M x y))
            ·
              have hca : a ≠ x := by simpa [ne_comm] using hxa
              have hcb : a ≠ y := by simpa [ne_comm] using hyb
              have hda : b ≠ x := by simpa [ne_comm] using hxb
              have hdb : b ≠ y := by simpa [ne_comm] using hya
              simpa [f] using
                (edgeBlocksOfInt_margin_other (a := x) (b := y) (c := a) (d := b)
                  (hne := hxy_ne) (hca := hca) (hcb := hcb)
                  (hda := hda) (hdb := hdb) (hcd := hne) (k := M x y))
    have hf0 : f (b, a) = M a b := by
      have hne' : b ≠ a := by exact Ne.symm hne
      have hsk : M b a = - M a b := by simpa [skew_symmetric] using hskew b a
      have hself :
          marginBlocks (edgeBlocksOfInt b a (M b a)) b a = M b a := by
        simpa [f] using
          (edgeBlocksOfInt_margin_ab (a := b) (b := a) hne' (k := M b a) (heven := heven b a))
      have hskew_blocks :
          marginBlocks (edgeBlocksOfInt b a (M b a)) a b =
            - marginBlocks (edgeBlocksOfInt b a (M b a)) b a :=
        marginBlocks_skew (blocks := edgeBlocksOfInt b a (M b a)) (a := a) (b := b) hne
      calc
        f (b, a) = marginBlocks (edgeBlocksOfInt b a (M b a)) a b := by rfl
        _ = - marginBlocks (edgeBlocksOfInt b a (M b a)) b a := hskew_blocks
        _ = - M b a := by simp [hself]
        _ = M a b := by simp [hsk]
    have hsum' :
        pairs.foldr (fun p acc => f p + acc) 0 = f (b, a) :=
      foldr_add_eq_of_mem f hnodup hp0_mem hzero
    simpa [hsum, hf0, f] using hsum'

theorem debordMcGarvey_fin (M : Fin n → Fin n → Int)
    (hskew : skew_symmetric M)
    (heven : ∀ a b, Even (M a b)) :
    ∃ (m : ℕ) (ballots : Fin m → ListBallot n),
      ∀ a b, margin (profileOfListBallots ballots) a b = M a b := by
  classical
  refine ⟨(ballotList (blocksForMargins (n := n) M)).length,
    ballotsOfList (ballotList (blocksForMargins (n := n) M)), ?_⟩
  intro a b
  by_cases hne : a = b
  · subst hne
    have h0 : M a a = 0 := by
      linarith [hskew a a]
    -- margins on the diagonal are zero by definition
    simpa [h0] using self_margin_zero (P := profileOfListBallots
      (ballotsOfList (ballotList (blocksForMargins (n := n) M)))) (a := a)
  ·
    have hmargin_blocks :
        margin (profileOfListBallots (ballotsOfList (ballotList (blocksForMargins (n := n) M)))) a b =
          marginBlocks (blocksForMargins (n := n) M) a b := by
      simpa [profileOfBlocks] using
        (margin_profileOfBlocks (blocks := blocksForMargins (n := n) M) (a := a) (b := b) hne)
    calc
      margin (profileOfListBallots (ballotsOfList (ballotList (blocksForMargins (n := n) M)))) a b
          = marginBlocks (blocksForMargins (n := n) M) a b := hmargin_blocks
      _ = M a b := blocksForMargins_margin (M := M) hskew heven (hne := hne)

section DebordMcGarveyOdd

def oddToEvenMargins (M : Fin n → Fin n → Int) : Fin n → Fin n → Int :=
  fun a b =>
    if a = b then 0 else if a < b then M a b - 1 else M a b + 1

lemma oddToEvenMargins_skew (M : Fin n → Fin n → Int)
    (hskew : skew_symmetric M) :
    skew_symmetric (oddToEvenMargins (n := n) M) := by
  intro a b
  by_cases h : a = b
  · subst h
    simp [oddToEvenMargins]
  · have hne : b ≠ a := by exact Ne.symm h
    cases lt_or_gt_of_ne h with
    | inl hlt =>
        have hnot : ¬ b < a := lt_asymm hlt
        have hsk : M b a = - M a b := by
          simpa [skew_symmetric] using hskew b a
        simp [oddToEvenMargins, h, hne, hlt, hnot, hsk] ; ring
    | inr hgt =>
        have hnot : ¬ a < b := not_lt_of_gt hgt
        have hsk : M b a = - M a b := by
          simpa [skew_symmetric] using hskew b a
        simp [oddToEvenMargins, h, hne, hnot, hgt, hsk] ; ring

lemma oddToEvenMargins_even (M : Fin n → Fin n → Int)
    (hodd : ∀ a b, a ≠ b → Odd (M a b)) :
    ∀ a b, Even (oddToEvenMargins (n := n) M a b) := by
  intro a b
  by_cases h : a = b
  · subst h
    simp [oddToEvenMargins]
  · cases lt_or_gt_of_ne h with
    | inl hlt =>
        have hnot : ¬ Even (M a b) := (Int.not_even_iff_odd).2 (hodd a b h)
        simpa [oddToEvenMargins, h, hlt] using (Int.even_sub_one).2 hnot
    | inr hgt =>
        have hnot : ¬ Even (M a b) := (Int.not_even_iff_odd).2 (hodd a b h)
        have hnot' : ¬ a < b := not_lt_of_gt hgt
        simpa [oddToEvenMargins, h, hnot'] using (Int.even_add_one).2 hnot

lemma marginOfBallot_identity (a b : Fin n) :
    marginOfBallot (ListBallot.identity n) a b = if a < b then 1 else -1 := by
  simp [marginOfBallot, prefersInList, ListBallot.identity]

theorem debordMcGarveyOdd_fin (M : Fin n → Fin n → Int)
    (hskew : skew_symmetric M)
    (hodd : ∀ a b, a ≠ b → Odd (M a b)) :
    ∃ (m : ℕ) (ballots : Fin m → ListBallot n),
      ∀ a b, margin (profileOfListBallots ballots) a b = M a b := by
  classical
  let M' : Fin n → Fin n → Int := oddToEvenMargins (n := n) M
  have hskew' : skew_symmetric M' := oddToEvenMargins_skew (n := n) (M := M) hskew
  have heven' : ∀ a b, Even (M' a b) := oddToEvenMargins_even (n := n) (M := M) hodd
  let blocks := blocksForMargins (n := n) M'
  let blocks' : List (Nat × ListBallot n) := blocks ++ [(1, ListBallot.identity n)]
  refine ⟨(ballotList blocks').length, ballotsOfList (ballotList blocks'), ?_⟩
  intro a b
  by_cases hne : a = b
  · subst hne
    have h0 : M a a = 0 := by
      linarith [hskew a a]
    -- margins on the diagonal are zero by definition
    simpa [h0] using self_margin_zero (P := profileOfListBallots
      (ballotsOfList (ballotList blocks'))) (a := a)
  ·
    have hmargin_blocks :
        margin (profileOfListBallots (ballotsOfList (ballotList blocks'))) a b =
          marginBlocks blocks' a b := by
      simpa [profileOfBlocks] using
        (margin_profileOfBlocks (blocks := blocks') (a := a) (b := b) hne)
    have hM' : marginBlocks blocks a b = M' a b := by
      simpa [blocks] using
        (blocksForMargins_margin (n := n) (M := M') hskew' heven' (hne := hne))
    have hblocks' :
        marginBlocks blocks' a b =
          marginBlocks blocks a b + marginBlocks [(1, ListBallot.identity n)] a b := by
      simpa [blocks'] using
        (marginBlocks_append (xs := blocks) (ys := [(1, ListBallot.identity n)]) (a := a) (b := b))
    have hid :
        marginBlocks [(1, ListBallot.identity n)] a b =
          marginOfBallot (ListBallot.identity n) a b := by
      simp [marginBlocks]
    cases lt_or_gt_of_ne hne with
    | inl hlt =>
        have hcalc :
            M' a b + marginOfBallot (ListBallot.identity n) a b = M a b := by
          simp [oddToEvenMargins, M', hne, hlt, marginOfBallot_identity]
        calc
          margin (profileOfListBallots (ballotsOfList (ballotList blocks'))) a b
              = marginBlocks blocks' a b := hmargin_blocks
          _ = marginBlocks blocks a b + marginBlocks [(1, ListBallot.identity n)] a b := hblocks'
          _ = M' a b + marginOfBallot (ListBallot.identity n) a b := by simp [hM', hid]
          _ = M a b := hcalc
    | inr hgt =>
        have hnot : ¬ a < b := not_lt_of_gt hgt
        have hcalc :
            M' a b + marginOfBallot (ListBallot.identity n) a b = M a b := by
          simp [oddToEvenMargins, M', hne, hnot, marginOfBallot_identity]
        calc
          margin (profileOfListBallots (ballotsOfList (ballotList blocks'))) a b
              = marginBlocks blocks' a b := hmargin_blocks
          _ = marginBlocks blocks a b + marginBlocks [(1, ListBallot.identity n)] a b := hblocks'
          _ = M' a b + marginOfBallot (ListBallot.identity n) a b := by simp [hM', hid]
          _ = M a b := hcalc

theorem debordMcGarveyOdd {A : Type} [Fintype A] [DecidableEq A]
    (M : A → A → Int)
    (hskew : skew_symmetric M)
    (hodd : ∀ a b, a ≠ b → Odd (M a b)) :
    ∃ (m : ℕ) (P : Profile (Fin m) A),
      ∀ a b, margin P a b = M a b := by
  classical
  let n : ℕ := Fintype.card A
  let e : A ≃ Fin n := Fintype.equivFin A
  let M' : Fin n → Fin n → Int := fun i j => M (e.symm i) (e.symm j)
  have hskew' : skew_symmetric M' := by
    intro i j
    simpa [M'] using hskew (e.symm i) (e.symm j)
  have hodd' : ∀ i j, i ≠ j → Odd (M' i j) := by
    intro i j hne
    simpa [M'] using hodd (e.symm i) (e.symm j) (by
      intro h
      apply hne
      simpa using congrArg e h)
  obtain ⟨m, ballots, hmargin⟩ := debordMcGarveyOdd_fin (n := n) M' hskew' hodd'
  refine ⟨m, relabelProfile (profileOfListBallots ballots) e.symm, ?_⟩
  intro a b
  simpa [margin_relabelProfile, M'] using hmargin (e a) (e b)

end DebordMcGarveyOdd

theorem debordMcGarvey {A : Type} [Fintype A] [DecidableEq A]
    (M : A → A → Int)
    (hskew : skew_symmetric M)
    (heven : ∀ a b, Even (M a b)) :
    ∃ (m : ℕ) (P : Profile (Fin m) A),
      ∀ a b, margin P a b = M a b := by
  classical
  let n : ℕ := Fintype.card A
  let e : A ≃ Fin n := Fintype.equivFin A
  let M' : Fin n → Fin n → Int := fun i j => M (e.symm i) (e.symm j)
  have hskew' : skew_symmetric M' := by
    intro i j
    simpa [M'] using hskew (e.symm i) (e.symm j)
  have heven' : ∀ i j, Even (M' i j) := by
    intro i j
    simpa [M'] using heven (e.symm i) (e.symm j)
  obtain ⟨m, ballots, hmargin⟩ := debordMcGarvey_fin (n := n) M' hskew' heven'
  refine ⟨m, relabelProfile (profileOfListBallots ballots) e.symm, ?_⟩
  intro a b
  simpa [margin_relabelProfile, M'] using hmargin (e a) (e b)

end DebordMcGarvey

end SocialChoice
