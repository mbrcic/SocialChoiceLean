import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Pairwise
import SocialChoice.Rules.River.Defs
import SocialChoice.Rules.River.Basic
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.SplitCycle.Clones
import SocialChoice.Meta

namespace SocialChoice

open Finset
attribute [local instance] Classical.decEq Classical.propDecidable

lemma hasIncoming_mono {A : Type} {E F : Finset (A × A)} (hEF : E ⊆ F) {y : A} :
    hasIncoming (A := A) E y → hasIncoming (A := A) F y := by
  intro h
  rcases h with ⟨x, hx⟩
  exact ⟨x, hEF hx⟩

lemma riverAddEdge_subset_insert {A : Type}
    (E : Finset (A × A)) (e : A × A) :
    riverAddEdge (A := A) E e ⊆ insert e E := by
  classical
  intro x hx
  dsimp [riverAddEdge] at hx
  split_ifs at hx with hcond
  · exact Finset.mem_insert.mpr (Or.inr hx)
  · exact hx

lemma riverAddEdge_superset {A : Type} (E : Finset (A × A)) (e : A × A) :
    E ⊆ riverAddEdge (A := A) E e := by
  classical
  by_cases hcond :
      hasIncoming (A := A) E e.2 ∨ hasCycle (A := A) (insert e E)
  · simp [riverAddEdge, hcond]
  · simp [riverAddEdge, hcond]

lemma foldl_subset_of_step {A : Type}
    (f : Finset (A × A) → (A × A) → Finset (A × A))
    (hf : ∀ E e, E ⊆ f E e) :
    ∀ l : List (A × A), ∀ E, E ⊆ List.foldl f E l
  | [], E => by
      simp
  | e :: t, E => by
      have hE : E ⊆ f E e := hf E e
      have hEt : f E e ⊆ List.foldl f (f E e) t :=
        foldl_subset_of_step (f := f) (hf := hf) (l := t) (E := f E e)
      exact hE.trans hEt

lemma list_mem_split {α : Type} {a : α} :
    ∀ {l : List α}, a ∈ l → ∃ l1 l2, l = l1 ++ a :: l2
  | [], h => by
      cases h
  | b :: t, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact ⟨[], t, rfl⟩
      · rcases list_mem_split (l := t) h' with ⟨l1, l2, htl⟩
        exact ⟨b :: l1, l2, by simp [htl]⟩

lemma riverDiagram_prefix_subset {A : Type} (l1 l2 : List (A × A)) :
    riverDiagram (A := A) l1 ⊆ riverDiagram (A := A) (l1 ++ l2) := by
  classical
  have hmono : ∀ E e, E ⊆ riverAddEdge (A := A) E e :=
    fun E e => riverAddEdge_superset (A := A) E e
  have hsubset :
      riverDiagram (A := A) l1 ⊆
        l2.foldl (riverAddEdge (A := A)) (riverDiagram (A := A) l1) := by
    exact foldl_subset_of_step (f := riverAddEdge (A := A)) hmono l2 (riverDiagram (A := A) l1)
  simpa [riverDiagram, List.foldl_append] using hsubset

lemma riverDiagram_foldl_subset {A : Type}
    (l : List (A × A)) (E : Finset (A × A)) :
    l.foldl (riverAddEdge (A := A)) E ⊆ E ∪ l.toFinset := by
  classical
  induction l generalizing E with
  | nil =>
      intro x hx
      exact (Finset.mem_union.mpr (Or.inl hx))
  | cons a t ih =>
      intro x hx
      have hx' :
          x ∈ riverAddEdge (A := A) E a ∪ t.toFinset := by
        exact ih (E := riverAddEdge (A := A) E a) hx
      rcases Finset.mem_union.mp hx' with hxE | hxT
      · have hxIns : x ∈ insert a E :=
          riverAddEdge_subset_insert (A := A) E a hxE
        rcases Finset.mem_insert.mp hxIns with rfl | hxE'
        · exact Finset.mem_union.mpr (Or.inr (by simp))
        · exact Finset.mem_union.mpr (Or.inl hxE')
      · exact Finset.mem_union.mpr (Or.inr (by simp [hxT]))

lemma riverDiagram_subset_toFinset {A : Type} (l : List (A × A)) :
    riverDiagram (A := A) l ⊆ l.toFinset := by
  classical
  intro x hx
  have hx' :
      x ∈ (∅ : Finset (A × A)) ∪ l.toFinset := by
    simpa [riverDiagram] using
      (riverDiagram_foldl_subset (A := A) (l := l) (E := (∅ : Finset (A × A))) hx)
  simpa using hx'

lemma cycle_contains_left_of_insert {A : Type} {E : Finset (A × A)}
    {e : A × A} {c : List A}
    (hcycle : cycle (edgeRel (A := A) (insert e E)) c)
    (hacyc : ¬ hasCycle (A := A) E) :
    e.1 ∈ c := by
  rcases hcycle with ⟨hne, hchain⟩
  by_contra hnot
  have hchain' :
      List.IsChain (edgeRel (A := A) E) (List.getLast c hne :: c) := by
    refine List.IsChain.imp_of_mem_tail_imp ?_ hchain
    intro a b ha _ hrel
    have ha_in_c : a ∈ c := by
      rcases List.mem_cons.mp ha with ha_eq | ha_mem
      · have : List.getLast c hne ∈ c := List.getLast_mem hne
        cases ha_eq
        exact this
      · exact ha_mem
    have ha_ne : a ≠ e.1 := by
      intro h_eq
      apply hnot
      simpa [h_eq] using ha_in_c
    rcases Finset.mem_insert.mp hrel with h_eq | h_in
    · have : a = e.1 := by
        simpa using congrArg Prod.fst h_eq
      exact (ha_ne this).elim
    · exact h_in
  have hcycleE : cycle (edgeRel (A := A) E) c := ⟨hne, hchain'⟩
  exact hacyc ⟨c, hcycleE⟩

lemma cycle_contains_right_of_insert {A : Type} {E : Finset (A × A)}
    {e : A × A} {c : List A}
    (hcycle : cycle (edgeRel (A := A) (insert e E)) c)
    (hacyc : ¬ hasCycle (A := A) E) :
    e.2 ∈ c := by
  rcases hcycle with ⟨hne, hchain⟩
  by_contra hnot
  have hchain' :
      List.IsChain (edgeRel (A := A) E) (List.getLast c hne :: c) := by
    refine List.IsChain.imp_of_mem_tail_imp ?_ hchain
    intro a b _ hb hrel
    have hb_in_c : b ∈ c := by
      simpa using hb
    have hb_ne : b ≠ e.2 := by
      intro h_eq
      apply hnot
      simpa [h_eq] using hb_in_c
    rcases Finset.mem_insert.mp hrel with h_eq | h_in
    · have : b = e.2 := by
        simpa using congrArg Prod.snd h_eq
      exact (hb_ne this).elim
    · exact h_in
  have hcycleE : cycle (edgeRel (A := A) E) c := ⟨hne, hchain'⟩
  exact hacyc ⟨c, hcycleE⟩

lemma pairwise_rel_of_mem_append {α : Type} {R : α → α → Prop}
    {l1 l2 : List α} {a b : α} :
    (l1 ++ b :: l2).Pairwise R → a ∈ l1 → R a b := by
  intro hpair ha
  induction l1 with
  | nil =>
      cases ha
  | cons x xs ih =>
      have hpair' :
          (∀ y ∈ xs ++ b :: l2, R x y) ∧ (xs ++ b :: l2).Pairwise R := by
        simpa [List.cons_append] using (List.pairwise_cons.mp hpair)
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hpair'.1 b (by simp)
      · exact ih hpair'.2 ha'

lemma descendingEdges_rel_of_mem_append {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {l1 l2 : List (A × A)} {e1 e2 : A × A} :
    descendingEdges (P := P) (l1 ++ e2 :: l2) →
      e1 ∈ l1 → edgeWeight P e1 >= edgeWeight P e2 := by
  intro hdesc hmem
  exact pairwise_rel_of_mem_append (R := fun x y => edgeWeight P x >= edgeWeight P y) hdesc hmem

lemma riverWinners_subset_splitCycle {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (tau : List (A × A)) (htau : isTiebreaker (P := P) tau) :
    riverWinners (A := A) tau ⊆ splitCycle P := by
  classical
  intro a ha
  have hnoIncoming :
      ¬ hasIncoming (A := A) (riverDiagram (A := A) tau) a := by
    exact (Finset.mem_filter.mp ha).2
  rcases htau with ⟨htau_nodup, htau_edges, htau_desc⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ a, ?_⟩
  intro b hdef
  have hpos : margin_pos P b a := hdef.1
  have hmemEdges : (b, a) ∈ marginEdges (P := P) := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    have : 0 <= edgeWeight P (b, a) := by
      simpa [edgeWeight] using (le_of_lt hpos)
    exact this
  have hmemTauFin : (b, a) ∈ tau.toFinset := by
    simpa [htau_edges] using hmemEdges
  have hmemTau : (b, a) ∈ tau := by
    exact List.mem_toFinset.mp hmemTauFin
  rcases list_mem_split hmemTau with ⟨l1, l2, htau_split⟩
  set e : A × A := (b, a)
  have htau_split' : tau = l1 ++ e :: l2 := by
    simpa [e] using htau_split
  let E : Finset (A × A) := riverDiagram (A := A) l1
  have hdesc : descendingEdges (P := P) (l1 ++ e :: l2) := by
    simpa [htau_split'] using htau_desc
  have hEsubset : E ⊆ l1.toFinset := by
    simpa [E] using (riverDiagram_subset_toFinset (A := A) (l := l1))
  have hacyc : ¬ hasCycle (A := A) E := by
    simpa [E] using (riverDiagram_noCycle (A := A) (tau := l1))
  have hsubset_prefix :
      E ⊆ riverDiagram (A := A) tau := by
    simpa [E, htau_split'] using
      (riverDiagram_prefix_subset (A := A) (l1 := l1) (l2 := e :: l2))
  have hnoIncomingE : ¬ hasIncoming (A := A) E a := by
    intro hinc
    exact hnoIncoming (hasIncoming_mono (A := A) hsubset_prefix hinc)
  have hnotMem : e ∉ riverDiagram (A := A) tau := by
    intro hmem
    have : hasIncoming (A := A) (riverDiagram (A := A) tau) a := by
      refine ⟨b, ?_⟩
      simpa [e] using hmem
    exact hnoIncoming this
  have hcycle : hasCycle (A := A) (insert e E) := by
    by_cases hcond :
        hasIncoming (A := A) E e.2 ∨ hasCycle (A := A) (insert e E)
    · rcases hcond with hinc | hcyc
      · exact (hnoIncomingE hinc).elim
      · exact hcyc
    · have hmem_step : e ∈ riverAddEdge (A := A) E e := by
        simp [riverAddEdge, hcond]
      have hmono : ∀ E e, E ⊆ riverAddEdge (A := A) E e :=
        fun E e => riverAddEdge_superset (A := A) E e
      have hsubset_step :
          riverAddEdge (A := A) E e ⊆
            l2.foldl (riverAddEdge (A := A)) (riverAddEdge (A := A) E e) := by
        exact foldl_subset_of_step (f := riverAddEdge (A := A)) hmono l2 (riverAddEdge (A := A) E e)
      have hdiagram :
          riverDiagram (A := A) tau =
            l2.foldl (riverAddEdge (A := A)) (riverAddEdge (A := A) E e) := by
        simp [riverDiagram, htau_split', E, List.foldl_append]
      have hmem_final : e ∈ riverDiagram (A := A) tau := by
        simpa [hdiagram] using (hsubset_step hmem_step)
      exact (hnotMem hmem_final).elim
  rcases hcycle with ⟨c, hcycle⟩
  have hb : b ∈ c := by
    have : e.1 ∈ c := cycle_contains_left_of_insert (A := A) (E := E) (e := e) (c := c)
      hcycle hacyc
    simpa [e] using this
  have ha' : a ∈ c := by
    have : e.2 ∈ c := cycle_contains_right_of_insert (A := A) (E := E) (e := e) (c := c)
      hcycle hacyc
    simpa [e] using this
  have hcycle_margin :
      cycle (fun x y => margin P b a ≤ margin P x y) c := by
    rcases hcycle with ⟨hne, hchain⟩
    have hchain' :
        List.IsChain (fun x y => edgeWeight P e ≤ edgeWeight P (x, y))
          (List.getLast c hne :: c) := by
      refine List.IsChain.imp_of_mem_imp ?_ hchain
      intro x y _ _ hrel
      rcases Finset.mem_insert.mp hrel with h_eq | h_in
      · simp [h_eq]
      · have h_in_l1 : (x, y) ∈ l1 := by
          have h_in_fin : (x, y) ∈ l1.toFinset := hEsubset h_in
          exact List.mem_toFinset.mp h_in_fin
        have hge :
            edgeWeight P (x, y) >= edgeWeight P e :=
          descendingEdges_rel_of_mem_append (P := P) (l1 := l1) (l2 := l2)
            (e1 := (x, y)) (e2 := e) hdesc h_in_l1
        exact hge
    have hchain'' :
        List.IsChain (fun x y => margin P b a ≤ margin P x y)
          (List.getLast c hne :: c) := by
      simpa [edgeWeight, e] using hchain'
    exact ⟨hne, hchain''⟩
  have hcycle_ex :
      ∃ c, b ∈ c ∧ a ∈ c ∧ cycle (fun x y => margin P b a ≤ margin P x y) c :=
    ⟨c, hb, ha', hcycle_margin⟩
  exact (hdef.2 hcycle_ex)

lemma river_subset_splitCycle_of_tiebreaker {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A)
    (h : ∀ tau : List (A × A), isTiebreaker (P := P) tau →
      riverWinners (A := A) tau ⊆ splitCycle P) :
    river P ⊆ splitCycle P := by
  classical
  intro a ha
  rcases (Finset.mem_filter.mp ha).2 with ⟨tau, htau, ha_tau⟩
  exact h tau htau ha_tau

/-- Reduce `river_refines_splitCycle` to the fixed-tiebreaker lemma. -/
theorem river_refines_splitCycle_of_tiebreaker
    (h : ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (tau : List (A × A)),
        isTiebreaker (P := P) tau → riverWinners (A := A) tau ⊆ splitCycle P) :
    Refines river splitCycle := by
  intro V A _ _ P
  exact river_subset_splitCycle_of_tiebreaker (P := P) (h (P := P))

theorem river_refines_splitCycle : Refines river splitCycle := by
  exact river_refines_splitCycle_of_tiebreaker
    (h := fun P tau htau => riverWinners_subset_splitCycle (P := P) (tau := tau) htau)

end SocialChoice
