import SocialChoice.Axioms.Reversal
import SocialChoice.Margin
import SocialChoice.Cycles
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

lemma margin_reverse_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin (reverse_profile P) b a = margin P a b := by
  classical
  simp [margin, prefers_reverse_profile]

lemma splitCycleDefeats_reverse_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    splitCycleDefeats (reverse_profile P) y x ↔ splitCycleDefeats P x y := by
  classical
  constructor
  · intro hdef
    rcases hdef with ⟨hpos, hnocycle⟩
    have hpos' : margin_pos P x y := by
      simpa [margin_pos, margin_reverse_eq] using hpos
    have hnocycle' :
        ¬ ∃ c : List A, x ∈ c ∧ y ∈ c ∧
          cycle (fun a b => margin P x y ≤ margin P a b) c := by
      intro hcyc
      rcases hcyc with ⟨c, hxmem, hymem, hcycle⟩
      have hcycle' :
          cycle (fun a b => margin (reverse_profile P) y x ≤
            margin (reverse_profile P) a b) c.reverse := by
        refine cycle_of_cycle_imp ?_ (cycle_reverse_rel (P := fun a b =>
          margin P x y ≤ margin P a b) hcycle)
        intro a b hab
        simpa [margin_reverse_eq] using hab
      have hxmem' : x ∈ c.reverse := by simpa using (List.mem_reverse.mpr hxmem)
      have hymem' : y ∈ c.reverse := by simpa using (List.mem_reverse.mpr hymem)
      exact hnocycle ⟨c.reverse, hymem', hxmem', hcycle'⟩
    exact ⟨hpos', hnocycle'⟩
  · intro hdef
    rcases hdef with ⟨hpos, hnocycle⟩
    have hpos' : margin_pos (reverse_profile P) y x := by
      simpa [margin_pos, margin_reverse_eq] using hpos
    have hnocycle' :
        ¬ ∃ c : List A, y ∈ c ∧ x ∈ c ∧
          cycle (fun a b => margin (reverse_profile P) y x ≤
            margin (reverse_profile P) a b) c := by
      intro hcyc
      rcases hcyc with ⟨c, hymem, hxmem, hcycle⟩
      have hcycle' :
          cycle (fun a b => margin P x y ≤ margin P a b) c.reverse := by
        refine cycle_of_cycle_imp ?_ (cycle_reverse_rel (P := fun a b =>
          margin (reverse_profile P) y x ≤ margin (reverse_profile P) a b) hcycle)
        intro a b hab
        simpa [margin_reverse_eq] using hab
      have hxmem' : x ∈ c.reverse := by simpa using (List.mem_reverse.mpr hxmem)
      have hymem' : y ∈ c.reverse := by simpa using (List.mem_reverse.mpr hymem)
      exact hnocycle ⟨c.reverse, hxmem', hymem', hcycle'⟩
    exact ⟨hpos', hnocycle'⟩

lemma splitCycleDefeats_acyclic {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : acyclic (splitCycleDefeats P) := by
  classical
  intro l hcycle
  rcases hcycle with ⟨hne, hchain⟩
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
  let L : List A := List.getLast l hne :: l
  let edgeMargin : Fin l.length → Int := fun j =>
    margin P (L.get j.castSucc) (L.get j.succ)
  have hnonempty : (Finset.univ : Finset (Fin l.length)).Nonempty := by
    refine ⟨⟨0, hlen⟩, by simp⟩
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image
    (s := (Finset.univ : Finset (Fin l.length))) (f := edgeMargin) hnonempty
  have hmin' : ∀ j : Fin l.length, edgeMargin i ≤ edgeMargin j := by
    intro j
    exact hmin j (by simp)
  set x : A := L.get i.castSucc
  set y : A := L.get i.succ
  have hchain_edges :
      ∀ j : Fin l.length, splitCycleDefeats P (L.get j.castSucc) (L.get j.succ) := by
    have hchain' :=
      (List.isChain_iff_getElem (R := splitCycleDefeats P) (l := L)).1 hchain
    intro j
    have hlt : j.val + 1 < L.length := by
      have hlt' : j.val + 1 < l.length + 1 := Nat.succ_lt_succ j.isLt
      simp [L, hlt']
    simpa using hchain' j.val hlt
  have hdef : splitCycleDefeats P x y := by
    simpa [x, y] using hchain_edges i
  rcases hdef with ⟨hpos, hnocycle⟩
  have hchainR :
      (List.getLast l hne :: l).IsChain (fun a b => margin P x y ≤ margin P a b) := by
    refine (List.isChain_iff_getElem
      (R := fun a b => margin P x y ≤ margin P a b) (l := L)).2 ?_
    intro k hk
    have hlt : k < l.length := by
      have hlt' : k + 1 < l.length + 1 := by
        simpa [L] using hk
      exact Nat.lt_of_succ_lt_succ hlt'
    let j : Fin l.length := ⟨k, hlt⟩
    have hminj : edgeMargin i ≤ edgeMargin j := hmin' j
    simpa [edgeMargin, x, y, L] using hminj
  have hcycle' : cycle (fun a b => margin P x y ≤ margin P a b) l := by
    exact ⟨hne, hchainR⟩
  have hxmem : x ∈ l := by
    have hxmemL : x ∈ L := List.get_mem _ _
    rcases List.mem_cons.mp hxmemL with hxmemL | hxmemL
    · have hxmemL' : l.getLast hne ∈ l := List.getLast_mem hne
      simp [hxmemL, hxmemL']
    · exact hxmemL
  have hymem : y ∈ l := by
    have hymemL : y ∈ L := List.get_mem _ _
    rcases List.mem_cons.mp hymemL with hymemL | hymemL
    · have hymemL' : l.getLast hne ∈ l := List.getLast_mem hne
      simp [hymemL, hymemL']
    · exact hymemL
  exact hnocycle ⟨l, hxmem, hymem, hcycle'⟩

theorem split_cycle_reversal_symmetry : reversal_symmetry splitCycle := by
  intro V A _ _ P x hnontriv hxwin
  classical
  have hxdef : ∃ y, splitCycleDefeats P x y := by
    -- derive an outgoing defeat from uniqueness + acyclicity.
    by_contra hnone
    have hnone' : ∀ y, ¬ splitCycleDefeats P x y := by
      intro y hy
      exact hnone ⟨y, hy⟩
    rcases hnontriv with ⟨y0, hy0⟩
    let S := {y : A // y ≠ x}
    let y0S : S := ⟨y0, by simpa [eq_comm] using hy0⟩
    have hdefeater : ∀ a : S, ∃ b : S, splitCycleDefeats P b.1 a.1 := by
      intro a
      have ha_notmem : a.1 ∉ splitCycle P := by
        intro ha_mem
        have : a.1 = x := by
          have : a.1 ∈ ({x} : Finset A) := by
            simpa [hxwin] using ha_mem
          simpa using (Finset.mem_singleton.mp this)
        exact a.property this
      have hnotall : ¬ ∀ y, ¬ splitCycleDefeats P y a.1 := by
        intro hall
        exact ha_notmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
      obtain ⟨b, hb⟩ := not_forall.mp hnotall
      have hb' : splitCycleDefeats P b a.1 := by
        exact not_not.mp hb
      have hbx : b ≠ x := by
        intro hEq
        subst hEq
        exact (hnone' a.1) hb'
      exact ⟨⟨b, hbx⟩, hb'⟩
    classical
    choose s hs using hdefeater
    let seq : ℕ → S := fun n => Nat.iterate s n y0S
    have hstep : ∀ n, splitCycleDefeats P (seq (n + 1)).1 (seq n).1 := by
      intro n
      simpa [seq, Function.iterate_succ_apply'] using (hs (seq n))
    have hni : ¬ Function.Injective seq :=
      not_injective_infinite_finite seq
    rcases (Function.not_injective_iff.1 hni) with ⟨i, j, hEq, hij⟩
    cases lt_or_gt_of_ne hij with
    | inl hlt =>
        have hmpos : 0 < j - i := Nat.sub_pos_of_lt hlt
        let m := j - i
        let a0 : S := seq i
        have hperiod : Nat.iterate s m a0 = a0 := by
          have hsum : i + m = j := Nat.add_sub_of_le (Nat.le_of_lt hlt)
          have hEq' : Nat.iterate s i y0S = Nat.iterate s j y0S := by
            simpa [seq] using hEq
          have hiter : Nat.iterate s (i + m) y0S = Nat.iterate s i y0S := by
            simpa [hsum] using hEq'.symm
          have hiter' : Nat.iterate s m a0 = Nat.iterate s (m + i) y0S := by
            simpa [a0, seq] using (Function.iterate_add_apply s m i y0S).symm
          calc
            Nat.iterate s m a0 = Nat.iterate s (m + i) y0S := hiter'
            _ = Nat.iterate s (i + m) y0S := by simp [Nat.add_comm]
            _ = Nat.iterate s i y0S := hiter
            _ = a0 := by simp [a0, seq]
        have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
        obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hmne
        let l : List S := List.iterate s a0 (Nat.succ m')
        have hlne : l ≠ [] := by
          simp [l]
        have hchain_l :
            l.IsChain (reverse_rel (fun a b : S => splitCycleDefeats P a.1 b.1)) := by
          simpa [l] using
            (isChain_iterate_reverse_rel
              (R := fun a b : S => splitCycleDefeats P a.1 b.1) (f := s)
              (h := fun a => hs a) (n := Nat.succ m') (a := a0))
        have hrel :
            ∀ x ∈ l.getLast?, ∀ y ∈ ([a0] : List S).head?,
              reverse_rel (fun a b : S => splitCycleDefeats P a.1 b.1) x y := by
          intro x hx y hy
          obtain ⟨hx', hxEq⟩ := List.mem_getLast?_eq_getLast (l := l) (x := x) hx
          have hyEq : y = a0 := by
            simpa [eq_comm] using hy
          subst hxEq
          subst hyEq
          have hlast : List.getLast l hlne = Nat.iterate s m' a0 := by
            simpa [l] using (getLast_iterate_succ s a0 m')
          have hperiod' : s (Nat.iterate s m' a0) = a0 := by
            simpa [Function.iterate_succ_apply', hm'] using hperiod
          have hdef : splitCycleDefeats P a0.1 (Nat.iterate s m' a0).1 := by
            have hdef' :
                splitCycleDefeats P (s (Nat.iterate s m' a0)).1 (Nat.iterate s m' a0).1 :=
              hs (Nat.iterate s m' a0)
            simpa [hperiod'] using hdef'
          simpa [reverse_rel, hlast] using hdef
        have hchain_append :
            (l ++ [a0]).IsChain
              (reverse_rel (fun a b : S => splitCycleDefeats P a.1 b.1)) := by
          refine List.IsChain.append hchain_l ?_ hrel
          exact (List.isChain_singleton (R := reverse_rel (fun a b : S =>
            splitCycleDefeats P a.1 b.1)) a0)
        have hchain_cycle :
            (a0 :: l.reverse).IsChain (fun a b : S => splitCycleDefeats P a.1 b.1) := by
          have hchain_rev :
              (l ++ [a0]).reverse.IsChain (fun a b : S => splitCycleDefeats P a.1 b.1) := by
            exact (List.isChain_reverse (R := fun a b : S => splitCycleDefeats P a.1 b.1)
              (l := l ++ [a0])).2 hchain_append
          simpa using hchain_rev
        let cS : List S := l.reverse
        have hne : cS ≠ [] := by
          intro hnil
          exact hlne (List.reverse_eq_nil_iff.mp hnil)
        have hlast : List.getLast cS hne = a0 := by
          have hlast' := getLast_reverse_eq_head (c := l) (hne := hlne)
          have hhead : l.head hlne = a0 := by
            simp [l]
          simp [cS, hhead, hlast']
        have hcycleS : cycle (fun a b : S => splitCycleDefeats P a.1 b.1) cS := by
          refine ⟨hne, ?_⟩
          simpa [cS, hlast] using hchain_cycle
        have hcycleA :
            cycle (splitCycleDefeats P) (cS.map Subtype.val) := by
          simpa using (cycle_map (f := Subtype.val) (P := splitCycleDefeats P) hcycleS)
        exact (splitCycleDefeats_acyclic P) _ hcycleA
    | inr hgt =>
        have hEq' : seq j = seq i := hEq.symm
        have hlt : j < i := hgt
        -- repeat the argument with swapped indices
        have hmpos : 0 < i - j := Nat.sub_pos_of_lt hlt
        let m := i - j
        let a0 : S := seq j
        have hperiod : Nat.iterate s m a0 = a0 := by
          have hsum : j + m = i := Nat.add_sub_of_le (Nat.le_of_lt hlt)
          have hEq'' : Nat.iterate s j y0S = Nat.iterate s i y0S := by
            simpa [seq] using hEq'
          have hiter : Nat.iterate s (j + m) y0S = Nat.iterate s j y0S := by
            simpa [hsum] using hEq''.symm
          have hiter' : Nat.iterate s m a0 = Nat.iterate s (m + j) y0S := by
            simpa [a0, seq] using (Function.iterate_add_apply s m j y0S).symm
          calc
            Nat.iterate s m a0 = Nat.iterate s (m + j) y0S := hiter'
            _ = Nat.iterate s (j + m) y0S := by simp [Nat.add_comm]
            _ = Nat.iterate s j y0S := hiter
            _ = a0 := by simp [a0, seq]
        have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
        obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hmne
        let l : List S := List.iterate s a0 (Nat.succ m')
        have hlne : l ≠ [] := by
          simp [l]
        have hchain_l :
            l.IsChain (reverse_rel (fun a b : S => splitCycleDefeats P a.1 b.1)) := by
          simpa [l] using
            (isChain_iterate_reverse_rel
              (R := fun a b : S => splitCycleDefeats P a.1 b.1) (f := s)
              (h := fun a => hs a) (n := Nat.succ m') (a := a0))
        have hrel :
            ∀ x ∈ l.getLast?, ∀ y ∈ ([a0] : List S).head?,
              reverse_rel (fun a b : S => splitCycleDefeats P a.1 b.1) x y := by
          intro x hx y hy
          obtain ⟨hx', hxEq⟩ := List.mem_getLast?_eq_getLast (l := l) (x := x) hx
          have hyEq : y = a0 := by
            simpa [eq_comm] using hy
          subst hxEq
          subst hyEq
          have hlast : List.getLast l hlne = Nat.iterate s m' a0 := by
            simpa [l] using (getLast_iterate_succ s a0 m')
          have hperiod' : s (Nat.iterate s m' a0) = a0 := by
            simpa [Function.iterate_succ_apply', hm'] using hperiod
          have hdef : splitCycleDefeats P a0.1 (Nat.iterate s m' a0).1 := by
            have hdef' :
                splitCycleDefeats P (s (Nat.iterate s m' a0)).1 (Nat.iterate s m' a0).1 :=
              hs (Nat.iterate s m' a0)
            simpa [hperiod'] using hdef'
          simpa [reverse_rel, hlast] using hdef
        have hchain_append :
            (l ++ [a0]).IsChain
              (reverse_rel (fun a b : S => splitCycleDefeats P a.1 b.1)) := by
          refine List.IsChain.append hchain_l ?_ hrel
          exact (List.isChain_singleton (R := reverse_rel (fun a b : S =>
            splitCycleDefeats P a.1 b.1)) a0)
        have hchain_cycle :
            (a0 :: l.reverse).IsChain (fun a b : S => splitCycleDefeats P a.1 b.1) := by
          have hchain_rev :
              (l ++ [a0]).reverse.IsChain (fun a b : S => splitCycleDefeats P a.1 b.1) := by
            exact (List.isChain_reverse (R := fun a b : S => splitCycleDefeats P a.1 b.1)
              (l := l ++ [a0])).2 hchain_append
          simpa using hchain_rev
        let cS : List S := l.reverse
        have hne : cS ≠ [] := by
          intro hnil
          exact hlne (List.reverse_eq_nil_iff.mp hnil)
        have hlast : List.getLast cS hne = a0 := by
          have hlast' := getLast_reverse_eq_head (c := l) (hne := hlne)
          have hhead : l.head hlne = a0 := by
            simp [l]
          simp [cS, hhead, hlast']
        have hcycleS : cycle (fun a b : S => splitCycleDefeats P a.1 b.1) cS := by
          refine ⟨hne, ?_⟩
          simpa [cS, hlast] using hchain_cycle
        have hcycleA :
            cycle (splitCycleDefeats P) (cS.map Subtype.val) := by
          simpa using (cycle_map (f := Subtype.val) (P := splitCycleDefeats P) hcycleS)
        exact (splitCycleDefeats_acyclic P) _ hcycleA
  rcases hxdef with ⟨y, hydef⟩
  have hydef' : splitCycleDefeats (reverse_profile P) y x := by
    simpa [splitCycleDefeats_reverse_iff] using hydef
  by_contra hxmem
  have hxcond : ∀ z, ¬ splitCycleDefeats (reverse_profile P) z x :=
    (Finset.mem_filter.mp hxmem).2
  exact (hxcond y) hydef'

end SocialChoice
