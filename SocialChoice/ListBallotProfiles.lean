import Mathlib.Data.Fin.Tuple.Basic
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

/-!
# Utilities for list-based profiles

This file provides basic list-level helpers for counterexamples:
bottom predicates, simple add/remove voter operations on `Fin`-indexed ballots,
and small simp lemmas for those operations.
-/

section BottomPredicates

variable {m n : ℕ}

/-- A list ballot is nonempty when `n ≠ 0`. -/
lemma ranking_ne_nil (b : ListBallot n) (hn : n ≠ 0) : b.ranking ≠ [] := by
  intro h
  have hlen := b.perm.length_eq
  simp [h, List.length_finRange] at hlen
  omega

/-- Check if candidate `c` is at the bottom of ballot `l`. -/
def isBottomOfList {α : Type} [DecidableEq α] (l : List α) (c : α) : Bool :=
  l.getLast? = some c

/-- Count how many voters rank candidate `c` at the bottom. -/
def countBottom (ballots : Fin m → List (Fin n)) (c : Fin n) : ℕ :=
  (Finset.univ.filter fun v => isBottomOfList (ballots v) c).card

end BottomPredicates

section AddRemoveVoters

variable {m n : ℕ}

/-- Remove the voter at position `i` from a list of ballots. -/
def removeVoterBallots (i : Fin (m + 1)) (ballots : Fin (m + 1) → ListBallot n) :
    Fin m → ListBallot n :=
  fun j => ballots (i.succAbove j)

/-- Insert a new ballot at position `i` in a list of ballots. -/
def insertVoterBallots (i : Fin (m + 1)) (b : ListBallot n) (ballots : Fin m → ListBallot n) :
    Fin (m + 1) → ListBallot n :=
  fun j => Fin.insertNth (α := fun _ => ListBallot n) i b (fun k => ballots k) j

@[simp] lemma insertVoterBallots_apply_same (i : Fin (m + 1)) (b : ListBallot n)
    (ballots : Fin m → ListBallot n) :
    insertVoterBallots i b ballots i = b := by
  simp [insertVoterBallots]

@[simp] lemma insertVoterBallots_apply_succAbove (i : Fin (m + 1)) (b : ListBallot n)
    (ballots : Fin m → ListBallot n) (j : Fin m) :
    insertVoterBallots i b ballots (i.succAbove j) = ballots j := by
  simp [insertVoterBallots]

@[simp] lemma removeVoterBallots_insertVoterBallots (i : Fin (m + 1)) (b : ListBallot n)
    (ballots : Fin m → ListBallot n) :
    removeVoterBallots i (insertVoterBallots i b ballots) = ballots := by
  funext j
  simp [removeVoterBallots]

end AddRemoveVoters

section ProfileOfLists

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- Build a profile from a list-valued ballot function with nodup/complete proofs. -/
noncomputable def profileOfLists (ballots : V → List A)
    (hnodup : ∀ v, (ballots v).Nodup)
    (hcomplete : ∀ v a, a ∈ ballots v) : Profile V A :=
  { pref := fun v => linearOrderOfList (ballots v) (hnodup v) (hcomplete v) }

lemma prefers_profileOfLists_iff_prefersInList (ballots : V → List A)
    (hnodup : ∀ v, (ballots v).Nodup)
    (hcomplete : ∀ v a, a ∈ ballots v) (v : V) (a b : A) :
    Prefers (profileOfLists ballots hnodup hcomplete) v a b ↔
      prefersInList (ballots v) a b = true := by
  unfold Prefers profileOfLists prefersInList
  simp [linearOrderOfList_lt_iff_idxOf, decide_eq_true_eq]

end ProfileOfLists

section ListLemmas

variable {α β : Type}

lemma mem_filterMap_iff {f : α → Option β} {b : β} {l : List α} :
    b ∈ l.filterMap f ↔ ∃ a ∈ l, f a = some b := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      cases hfa : f a with
      | none =>
          constructor
          · intro hb
            have hb' : b ∈ l.filterMap f := by
              simpa [List.filterMap, hfa] using hb
            rcases (ih.mp hb') with ⟨a', ha', hfa'⟩
            exact ⟨a', (List.mem_cons).2 (Or.inr ha'), hfa'⟩
          · intro h
            rcases h with ⟨a', ha', hfa'⟩
            have ha'' : a' = a ∨ a' ∈ l := by
              simpa using (List.mem_cons).1 ha'
            cases ha'' with
            | inl hEq =>
                subst hEq
                simp [hfa] at hfa'
            | inr hmem =>
                have hb' : b ∈ l.filterMap f := ih.mpr ⟨a', hmem, hfa'⟩
                simpa [List.filterMap, hfa] using hb'
      | some val =>
          constructor
          · intro hb
            have hb' : b = val ∨ b ∈ l.filterMap f := by
              simpa [List.filterMap, hfa] using hb
            cases hb' with
            | inl hEq =>
                refine ⟨a, (List.mem_cons).2 (Or.inl rfl), ?_⟩
                simp [hfa, hEq]
            | inr hmem =>
                rcases (ih.mp hmem) with ⟨a', ha', hfa'⟩
                exact ⟨a', (List.mem_cons).2 (Or.inr ha'), hfa'⟩
          · intro h
            rcases h with ⟨a', ha', hfa'⟩
            have ha'' : a' = a ∨ a' ∈ l := by
              simpa using (List.mem_cons).1 ha'
            cases ha'' with
            | inl hEq =>
                subst hEq
                have hEq' : val = b := by
                  simpa [hfa] using hfa'
                simp [List.filterMap, hfa, hEq'.symm]
            | inr hmem =>
                have hb' : b ∈ l.filterMap f := ih.mpr ⟨a', hmem, hfa'⟩
                simp [List.filterMap, hfa, hb']

end ListLemmas

section CandidateRemoval

variable {m n : ℕ}

/-- Remove a candidate from a ranking list, producing a list over the subtype. -/
def removeCandidateList (c : Fin n) (l : List (Fin n)) : List {x : Fin n // x ≠ c} :=
  l.filterMap (fun x => if h : x ≠ c then some ⟨x, h⟩ else none)

lemma prefersInList_removeCandidateList_iff (c : Fin n) (l : List (Fin n))
    (a b : {x : Fin n // x ≠ c}) (ha : (a : Fin n) ∈ l) (hb : (b : Fin n) ∈ l) :
    prefersInList (removeCandidateList c l) a b = true ↔
      prefersInList l a b = true := by
  classical
  let _ : BEq {x : Fin n // x ≠ c} := instBEqOfDecidableEq
  let _ : LawfulBEq {x : Fin n // x ≠ c} := by infer_instance
  unfold prefersInList
  simp [decide_eq_true_eq]
  induction l with
  | nil =>
      cases ha
  | cons x xs ih =>
      by_cases hx_c : x = c
      · have ha' : (a : Fin n) ∈ xs := by
          have hne : (a : Fin n) ≠ x := by simpa [hx_c] using a.property
          simpa [List.mem_cons, hne] using ha
        have hb' : (b : Fin n) ∈ xs := by
          have hne : (b : Fin n) ≠ x := by simpa [hx_c] using b.property
          simpa [List.mem_cons, hne] using hb
        have hidx_a : List.idxOf (a : Fin n) (x :: xs) = Nat.succ (List.idxOf (a : Fin n) xs) := by
          simpa [List.idxOf_cons, beq_false_of_ne (by simpa [hx_c] using (Ne.symm a.property))] using
            (List.idxOf_cons_ne (l := xs) (a := (a : Fin n)) (b := x)
              (by simpa [hx_c] using a.property.symm))
        have hidx_b : List.idxOf (b : Fin n) (x :: xs) = Nat.succ (List.idxOf (b : Fin n) xs) := by
          simpa [List.idxOf_cons, beq_false_of_ne (by simpa [hx_c] using (Ne.symm b.property))] using
            (List.idxOf_cons_ne (l := xs) (a := (b : Fin n)) (b := x)
              (by simpa [hx_c] using b.property.symm))
        have hih :
            List.idxOf a (removeCandidateList c xs) < List.idxOf b (removeCandidateList c xs) ↔
              List.idxOf (↑a) xs < List.idxOf (↑b) xs := by
          simpa using (ih ha' hb')
        calc
          List.idxOf a (removeCandidateList c (x :: xs)) < List.idxOf b (removeCandidateList c (x :: xs)) ↔
              List.idxOf a (removeCandidateList c xs) < List.idxOf b (removeCandidateList c xs) := by
                simp [removeCandidateList, hx_c]
          _ ↔ List.idxOf (↑a) xs < List.idxOf (↑b) xs := hih
          _ ↔ List.idxOf (↑a) (x :: xs) < List.idxOf (↑b) (x :: xs) := by
                simp [hidx_a, hidx_b]
      · by_cases hx_a : x = (a : Fin n)
        · by_cases hx_b : x = (b : Fin n)
          · have hxab : a = b := by
              apply Subtype.ext
              simpa [hx_a] using hx_b
            subst hxab
            simp [removeCandidateList, hx_a, List.idxOf_cons_self]
          · subst hx_a
            have hx_b_sub : (⟨(a : Fin n), a.property⟩ : {x : Fin n // x ≠ c}) ≠ b := by
              intro h
              have := congrArg Subtype.val h
              exact hx_b (by simpa using this)
            have hidx_a_remove : List.idxOf a (removeCandidateList c ((a : Fin n) :: xs)) = 0 := by
              simp [removeCandidateList, hx_c]
            have hidx_b_remove :
                List.idxOf b (removeCandidateList c ((a : Fin n) :: xs)) =
                  Nat.succ (List.idxOf b (removeCandidateList c xs)) := by
              simp [removeCandidateList, hx_c, hx_b_sub, List.idxOf_cons_ne]
            have hidx_a : List.idxOf (↑a) ((a : Fin n) :: xs) = 0 := by
              simp
            have hidx_b : List.idxOf (↑b) ((a : Fin n) :: xs) = Nat.succ (List.idxOf (↑b) xs) := by
              simp [List.idxOf_cons_ne, hx_b]
            simp [hidx_a_remove, hidx_b_remove, hidx_a, hidx_b]
        · by_cases hx_b : x = (b : Fin n)
          · subst hx_b
            have hx_a_sub : (⟨(b : Fin n), b.property⟩ : {x : Fin n // x ≠ c}) ≠ a := by
              intro h
              have := congrArg Subtype.val h
              exact hx_a (by simpa using this)
            have hidx_b_remove : List.idxOf b (removeCandidateList c ((b : Fin n) :: xs)) = 0 := by
              simp [removeCandidateList, hx_c]
            have hidx_a_remove :
                List.idxOf a (removeCandidateList c ((b : Fin n) :: xs)) =
                  Nat.succ (List.idxOf a (removeCandidateList c xs)) := by
              simp [removeCandidateList, hx_c, hx_a_sub, List.idxOf_cons_ne]
            have hidx_b : List.idxOf (↑b) ((b : Fin n) :: xs) = 0 := by
              simp
            have hidx_a : List.idxOf (↑a) ((b : Fin n) :: xs) = Nat.succ (List.idxOf (↑a) xs) := by
              simp [List.idxOf_cons_ne, hx_a]
            simp [hidx_a_remove, hidx_b_remove, hidx_a, hidx_b]
          · have ha' : (a : Fin n) ∈ xs := by
              have ha'' := (List.mem_cons).1 ha
              cases ha'' with
              | inl hEq =>
                  exact (False.elim (hx_a (by simpa using hEq.symm)))
              | inr hmem => exact hmem
            have hb' : (b : Fin n) ∈ xs := by
              have hb'' := (List.mem_cons).1 hb
              cases hb'' with
              | inl hEq =>
                  exact (False.elim (hx_b (by simpa using hEq.symm)))
              | inr hmem => exact hmem
            have hx_a_sub : (⟨x, hx_c⟩ : {x : Fin n // x ≠ c}) ≠ a := by
              intro h
              have := congrArg Subtype.val h
              exact hx_a (by simpa using this)
            have hx_b_sub : (⟨x, hx_c⟩ : {x : Fin n // x ≠ c}) ≠ b := by
              intro h
              have := congrArg Subtype.val h
              exact hx_b (by simpa using this)
            have hidx_a_remove :
                List.idxOf a (removeCandidateList c (x :: xs)) =
                  Nat.succ (List.idxOf a (removeCandidateList c xs)) := by
              simp [removeCandidateList, hx_c, hx_a_sub, List.idxOf_cons_ne]
            have hidx_b_remove :
                List.idxOf b (removeCandidateList c (x :: xs)) =
                  Nat.succ (List.idxOf b (removeCandidateList c xs)) := by
              simp [removeCandidateList, hx_c, hx_b_sub, List.idxOf_cons_ne]
            have hidx_a :
                List.idxOf (↑a) (x :: xs) = Nat.succ (List.idxOf (↑a) xs) := by
              simp [hx_a]
            have hidx_b :
                List.idxOf (↑b) (x :: xs) = Nat.succ (List.idxOf (↑b) xs) := by
              simp [hx_b]
            have hih :
                List.idxOf a (removeCandidateList c xs) < List.idxOf b (removeCandidateList c xs) ↔
                  List.idxOf (↑a) xs < List.idxOf (↑b) xs := by
              simpa using (ih ha' hb')
            calc
              List.idxOf a (removeCandidateList c (x :: xs)) < List.idxOf b (removeCandidateList c (x :: xs)) ↔
                  List.idxOf a (removeCandidateList c xs) < List.idxOf b (removeCandidateList c xs) := by
                    simp [hidx_a_remove, hidx_b_remove]
              _ ↔ List.idxOf (↑a) xs < List.idxOf (↑b) xs := hih
              _ ↔ List.idxOf (↑a) (x :: xs) < List.idxOf (↑b) (x :: xs) := by
                    simp [hidx_a, hidx_b]

lemma removeCandidateList_nodup (c : Fin n) (l : List (Fin n)) (hnodup : l.Nodup) :
    (removeCandidateList c l).Nodup := by
  classical
  let f : Fin n → Option {x : Fin n // x ≠ c} :=
    fun x => if h : x ≠ c then some ⟨x, h⟩ else none
  have hinj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a' := by
    intro a a' b hb hb'
    by_cases ha : a ≠ c
    · by_cases ha' : a' ≠ c
      · have hb1 : (⟨a, ha⟩ : {x : Fin n // x ≠ c}) = b := by
          simpa [f, ha] using hb
        have hb2 : (⟨a', ha'⟩ : {x : Fin n // x ≠ c}) = b := by
          simpa [f, ha'] using hb'
        have hsub :
            (⟨a, ha⟩ : {x : Fin n // x ≠ c}) = ⟨a', ha'⟩ := by
          exact hb1.trans hb2.symm
        have := congrArg Subtype.val hsub
        simpa using this
      · simp [f, ha'] at hb'
    · simp [f, ha] at hb
  simpa [removeCandidateList, f] using (List.Nodup.filterMap hinj hnodup)

lemma removeCandidateList_complete (c : Fin n) (l : List (Fin n)) (hcomplete : ∀ a, a ∈ l) :
    ∀ x : {y : Fin n // y ≠ c}, x ∈ removeCandidateList c l := by
  intro x
  have hx : x.1 ∈ l := hcomplete x.1
  have hx' :
      ∃ a ∈ l,
        (if h : a ≠ c then some ⟨a, h⟩ else none) = some x := by
    refine ⟨x.1, hx, ?_⟩
    simp [x.property]
  simpa [removeCandidateList] using
    (mem_filterMap_iff (f := fun a => if h : a ≠ c then some ⟨a, h⟩ else none)
      (b := x) (l := l)).2 hx'

/-- Remove a candidate from each ballot list. -/
def removeCandidateBallots (c : Fin n) (ballots : Fin m → ListBallot n) :
    Fin m → List {x : Fin n // x ≠ c} :=
  fun v => removeCandidateList c (ballots v).ranking

/-- A profile obtained by removing a candidate from list ballots. -/
noncomputable def profileOfListBallots_removeCandidate_list
    (ballots : Fin m → ListBallot n) (c : Fin n) :
    Profile (Fin m) {x : Fin n // x ≠ c} :=
  profileOfLists (ballots := removeCandidateBallots c ballots)
    (hnodup := fun v =>
      removeCandidateList_nodup (c := c) (l := (ballots v).ranking) (ballots v).nodup)
    (hcomplete := fun v a =>
      removeCandidateList_complete (c := c) (l := (ballots v).ranking)
        (ballots v).complete a)

/-- Candidate removal at the profile level (ties to `restrictProfile`). -/
noncomputable def profileOfListBallots_removeCandidate
    (ballots : Fin m → ListBallot n) (c : Fin n) :
    Profile (Fin m) {x : Fin n // x ≠ c} :=
  restrictProfile (profileOfListBallots ballots) c

@[simp] lemma profileOfListBallots_removeCandidate_eq
    (ballots : Fin m → ListBallot n) (c : Fin n) :
    profileOfListBallots_removeCandidate ballots c =
      restrictProfile (profileOfListBallots ballots) c := by
  rfl

lemma profileOfListBallots_removeCandidate_list_eq
    (ballots : Fin m → ListBallot n) (c : Fin n) :
    profileOfListBallots_removeCandidate_list ballots c =
      restrictProfile (profileOfListBallots ballots) c := by
  classical
  apply Profile.ext
  intro v
  apply LinearOrder.ext_lt
  intro a b
  change
    Prefers (profileOfListBallots_removeCandidate_list ballots c) v a b ↔
      Prefers (restrictProfile (profileOfListBallots ballots) c) v a b
  have ha : (a : Fin n) ∈ (ballots v).ranking := (ballots v).complete a
  have hb : (b : Fin n) ∈ (ballots v).ranking := (ballots v).complete b
  have hleft :
      Prefers (profileOfListBallots_removeCandidate_list ballots c) v a b ↔
        prefersInList (removeCandidateList c (ballots v).ranking) a b = true := by
    simpa [profileOfListBallots_removeCandidate_list, profileOfLists, removeCandidateBallots] using
      (prefers_profileOfLists_iff_prefersInList
        (ballots := removeCandidateBallots c ballots)
        (hnodup := fun v =>
          removeCandidateList_nodup (c := c) (l := (ballots v).ranking) (ballots v).nodup)
        (hcomplete := fun v a =>
          removeCandidateList_complete (c := c) (l := (ballots v).ranking)
            (ballots v).complete a)
        v a b)
  have hrem :
      prefersInList (removeCandidateList c (ballots v).ranking) a b = true ↔
        prefersInList (ballots v).ranking a b = true := by
    exact prefersInList_removeCandidateList_iff (c := c) (l := (ballots v).ranking) (a := a) (b := b) ha hb
  have horig :
      Prefers (profileOfListBallots ballots) v a b ↔
        prefersInList (ballots v).ranking a b = true := by
    simpa using (prefers_iff_prefersInList (ballots := ballots) (v := v)
      (a := (a : Fin n)) (b := (b : Fin n)))
  have hrest :
      Prefers (restrictProfile (profileOfListBallots ballots) c) v a b ↔
        Prefers (profileOfListBallots ballots) v a b := by
    rfl
  calc
    Prefers (profileOfListBallots_removeCandidate_list ballots c) v a b
        ↔ prefersInList (removeCandidateList c (ballots v).ranking) a b = true := hleft
    _ ↔ prefersInList (ballots v).ranking a b = true := hrem
    _ ↔ Prefers (profileOfListBallots ballots) v a b := horig.symm
    _ ↔ Prefers (restrictProfile (profileOfListBallots ballots) c) v a b := hrest.symm

end CandidateRemoval

section BottomLemmas

variable {m n : ℕ}

lemma bottomRank_iff_isBottomOfList (ballots : Fin m → ListBallot n) (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      isBottomOfList (ballots v).ranking c = true := by
  constructor
  · intro hbot
    by_cases hn : n = 0
    · exact Fin.elim0 (hn ▸ c)
    · have hne : (ballots v).ranking ≠ [] := ranking_ne_nil (ballots v) hn
      have hlast_not_mem :
          (ballots v).ranking.getLast hne ∉ (ballots v).ranking.dropLast := by
        have hnodup : (ballots v).ranking.Nodup := (ballots v).nodup
        have hnodup' :
            ((ballots v).ranking.dropLast ++ [(ballots v).ranking.getLast hne]).Nodup := by
          simpa [List.dropLast_append_getLast hne] using hnodup
        have hdisj :
            List.Disjoint (ballots v).ranking.dropLast
              ([(ballots v).ranking.getLast hne]) := by
          exact (List.Nodup.disjoint hnodup')
        intro hmem
        have hmem' : (ballots v).ranking.getLast hne ∈
            ([(ballots v).ranking.getLast hne]) := by simp
        exact (List.disjoint_left.mp hdisj) hmem hmem'
      have hidx_last :
          (ballots v).ranking.idxOf ((ballots v).ranking.getLast hne) =
            (ballots v).ranking.length - 1 := by
        exact List.idxOf_getLast hne hlast_not_mem
      have hlast_eq : (ballots v).ranking.getLast hne = c := by
        by_contra hne_last
        have hlt : (ballots v).ranking.idxOf ((ballots v).ranking.getLast hne) <
            (ballots v).ranking.idxOf c := by
          have hpref :
              Prefers (profileOfListBallots ballots) v
                ((ballots v).ranking.getLast hne) c := by
            exact hbot _ hne_last
          unfold Prefers profileOfListBallots at hpref
          simpa [(ballots v).lt_iff_idxOf] using hpref
        have hidx_c_lt : (ballots v).ranking.idxOf c <
            (ballots v).ranking.length := by
          exact List.idxOf_lt_length_of_mem ((ballots v).complete c)
        have hle : (ballots v).ranking.idxOf c ≤ (ballots v).ranking.length - 1 :=
          Nat.le_pred_of_lt hidx_c_lt
        have hcontra : (ballots v).ranking.length - 1 <
            (ballots v).ranking.idxOf c := by
          simpa [hidx_last] using hlt
        exact (Nat.not_lt_of_ge hle hcontra)
      unfold isBottomOfList
      have hlast? :
          (ballots v).ranking.getLast? = some ((ballots v).ranking.getLast hne) := by
        simp [List.getLast?_eq_getLast_of_ne_nil hne]
      simp [hlast_eq, hlast?]
  · intro hbottom
    by_cases hn : n = 0
    · exact Fin.elim0 (hn ▸ c)
    · have hne : (ballots v).ranking ≠ [] := ranking_ne_nil (ballots v) hn
      have hlast? :
          (ballots v).ranking.getLast? = some ((ballots v).ranking.getLast hne) := by
        simp [List.getLast?_eq_getLast_of_ne_nil hne]
      have hlast_eq : (ballots v).ranking.getLast hne = c := by
        unfold isBottomOfList at hbottom
        simpa [hlast?] using hbottom
      intro d hd
      have hmem : d ∈ (ballots v).ranking := (ballots v).complete d
      have hne_last : d ≠ (ballots v).ranking.getLast hne := by
        simpa [hlast_eq] using hd
      have hmem_drop :
          d ∈ (ballots v).ranking.dropLast := by
        exact List.mem_dropLast_of_mem_of_ne_getLast hmem hne_last
      have hidx_d :
          (ballots v).ranking.idxOf d < (ballots v).ranking.length - 1 := by
        exact (List.mem_dropLast_iff_idxOf_lt hmem).1 hmem_drop
      have hidx_last :
          (ballots v).ranking.idxOf ((ballots v).ranking.getLast hne) =
            (ballots v).ranking.length - 1 := by
        have hnodup : (ballots v).ranking.Nodup := (ballots v).nodup
        have hnodup' :
            ((ballots v).ranking.dropLast ++ [(ballots v).ranking.getLast hne]).Nodup := by
          simpa [List.dropLast_append_getLast hne] using hnodup
        have hdisj :
            List.Disjoint (ballots v).ranking.dropLast
              ([(ballots v).ranking.getLast hne]) := by
          exact (List.Nodup.disjoint hnodup')
        have hlast_not_mem :
            (ballots v).ranking.getLast hne ∉ (ballots v).ranking.dropLast := by
          intro hmem'
          have hmem'' :
              (ballots v).ranking.getLast hne ∈
                ([(ballots v).ranking.getLast hne]) := by simp
          exact (List.disjoint_left.mp hdisj) hmem' hmem''
        exact List.idxOf_getLast hne hlast_not_mem
      have hidx_c :
          (ballots v).ranking.idxOf c = (ballots v).ranking.length - 1 := by
        simpa [hlast_eq] using hidx_last
      have hlt :
          (ballots v).ranking.idxOf d <
            (ballots v).ranking.idxOf c := by
        simpa [hidx_c] using hidx_d
      unfold Prefers profileOfListBallots
      simpa [(ballots v).lt_iff_idxOf] using hlt

lemma votersBottom_eq_filter_isBottomOfList (ballots : Fin m → ListBallot n) (c : Fin n) :
    votersBottom (profileOfListBallots ballots) c =
      Finset.univ.filter (fun v => isBottomOfList (ballots v).ranking c) := by
  ext v
  simp [votersBottom, bottomRank_iff_isBottomOfList]

lemma votersBottom_card_eq_countBottom (ballots : Fin m → ListBallot n) (c : Fin n) :
    (votersBottom (profileOfListBallots ballots) c).card =
      countBottom (fun v => (ballots v).ranking) c := by
  unfold countBottom
  rw [votersBottom_eq_filter_isBottomOfList]

end BottomLemmas

section TopLemmas

variable {m n : ℕ}

lemma topRank_iff_isTopOfList_list (ballots : Fin m → ListBallot n) (v : Fin m) (c : Fin n) :
    TopRank (profileOfListBallots ballots) v c ↔
      isTopOfList (ballots v).ranking c = true := by
  simpa using (topRank_iff_isTopOfList ballots v c)

lemma votersTop_eq_filter_isTopOfList_list (ballots : Fin m → ListBallot n) (c : Fin n) :
    votersTop (profileOfListBallots ballots) c =
      Finset.univ.filter (fun v => isTopOfList (ballots v).ranking c) := by
  simpa using (votersTop_eq_filter_isTopOfList ballots c)

lemma votersTop_card_eq_countTop_list (ballots : Fin m → ListBallot n) (c : Fin n) :
    (votersTop (profileOfListBallots ballots) c).card =
      countTop (fun v => (ballots v).ranking) c := by
  simpa using (votersTop_card_eq_countTop ballots c)

end TopLemmas

section ScoreLemmas

variable {m n : ℕ}

open scoped BigOperators

/-- List-level scoring using `rank` from list ballots. -/
noncomputable def scoreList (ballots : Fin m → ListBallot n) (score : Nat → Int) (c : Fin n) :
    Int :=
  (Finset.univ : Finset (Fin m)).sum (fun v => score (rank (ballots v).toLinearOrder c))

lemma scoreCandidate_profileOfListBallots (ballots : Fin m → ListBallot n) (score : Nat → Int)
    (c : Fin n) :
    scoreCandidate (profileOfListBallots ballots) score c = scoreList ballots score c := by
  rfl

end ScoreLemmas

end SocialChoice
