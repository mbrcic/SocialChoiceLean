import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Axioms.Condorcet
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

namespace SocialChoice

open Finset

/-!
# ListBallot Infrastructure

This file provides utilities for constructing profiles from list-based ballots,
along with computable predicates and bridge lemmas connecting them to the
abstract Profile/LinearOrder definitions. This is useful for reasoning about
concrete examples in a computational way.

## Main definitions

* `ListBallot n` - A ballot represented as a permutation of `finRange n`
* `ListBallot.toLinearOrder` - Convert a ListBallot to a LinearOrder
* `profileOfListBallots` - Construct a Profile from ListBallots
* `isTopOfList`, `prefersInList` - Computable predicates on lists

## Bridge lemmas

* `listBallot_lt_iff_idxOf` - lt in the LinearOrder ↔ idxOf comparison
* `topRank_iff_isTopOfList` - TopRank ↔ isTopOfList
* `prefers_iff_prefersInList` - Prefers ↔ prefersInList
-/

/-! ### LinearOrder from List -/

section LinearOrderFromList

variable {A : Type*} [DecidableEq A]

/--
Construct a `LinearOrder` from a nodup list that covers all elements of a type.
The order is: `a < b` iff `a` appears before `b` in the list.
-/
noncomputable def linearOrderOfList (l : List A)
    (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) : LinearOrder A :=
  let e := List.Nodup.getEquivOfForallMemList l hnodup hcomplete
  LinearOrder.lift' e.symm e.symm.injective

lemma linearOrderOfList_lt (l : List A) (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) (a b : A) :
    (linearOrderOfList l hnodup hcomplete).lt a b ↔
      (List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm a <
      (List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm b := by
  rfl

end LinearOrderFromList

/-! ### ListBallot Structure -/

section ListBallot

/--
A `ListBallot n` is a ranking of `Fin n` represented as a list,
where the first element is the most preferred candidate.
It must be a permutation of `finRange n`.
-/
structure ListBallot (n : ℕ) where
  ranking : List (Fin n)
  perm : ranking.Perm (List.finRange n)

namespace ListBallot

variable {n : ℕ}

/-- A ListBallot has no duplicates (follows from being a permutation). -/
lemma nodup (b : ListBallot n) : b.ranking.Nodup :=
  b.perm.nodup_iff.mpr (List.nodup_finRange n)

/-- Every element of Fin n appears in a ListBallot. -/
lemma complete (b : ListBallot n) (a : Fin n) : a ∈ b.ranking :=
  b.perm.mem_iff.mpr (List.mem_finRange a)

/-- Convert a ListBallot to a LinearOrder. -/
noncomputable def toLinearOrder (b : ListBallot n) : LinearOrder (Fin n) :=
  linearOrderOfList b.ranking b.nodup b.complete

/-- The lt relation of toLinearOrder corresponds to idxOf comparison. -/
lemma lt_iff_idxOf (b : ListBallot n) (a c : Fin n) :
    b.toLinearOrder.lt a c ↔ b.ranking.idxOf a < b.ranking.idxOf c := by
  rfl

/-- Create a ListBallot from a list with a decidable permutation proof. -/
def mk' (l : List (Fin n)) (h : l.Perm (List.finRange n) := by decide) : ListBallot n :=
  ⟨l, h⟩

/-- The identity ballot [0, 1, 2, ..., n-1]. -/
def identity (n : ℕ) : ListBallot n :=
  ⟨List.finRange n, List.Perm.refl _⟩

end ListBallot

end ListBallot

/-! ### Profile from ListBallots -/

section ProfileOfListBallots

variable {m n : ℕ}

/-- Construct a Profile from a function assigning ListBallots to voters. -/
noncomputable def profileOfListBallots (ballots : Fin m → ListBallot n) : Profile (Fin m) (Fin n) where
  pref := fun v => (ballots v).toLinearOrder

/-- Access the underlying ranking list for a voter in a list-based profile. -/
def profileBallotRanking (ballots : Fin m → ListBallot n) (v : Fin m) : List (Fin n) :=
  (ballots v).ranking

end ProfileOfListBallots

/-! ### Computable Predicates -/

section ComputablePredicates

variable {α : Type*} [DecidableEq α]

/-- Check if candidate `c` is at the top of ballot `l`. -/
def isTopOfList (l : List α) (c : α) : Bool :=
  l.head? = some c

/-- Check if `a` is preferred to `b` in ballot `l` (a appears before b). -/
def prefersInList (l : List α) (a b : α) : Bool :=
  l.idxOf a < l.idxOf b

/-- Get the position (0-indexed) of candidate `c` in ballot `l`. -/
def positionInList (l : List α) (c : α) : ℕ :=
  l.idxOf c

/-- Borda score: n - 1 - position (top candidate gets n-1 points). -/
def bordaScoreInList (l : List α) (c : α) : ℕ :=
  l.length - 1 - l.idxOf c

end ComputablePredicates

/-! ### Aggregate Computations -/

section AggregateComputations

variable {m n : ℕ}

/-- Count how many voters rank candidate `c` on top. -/
def countTop (ballots : Fin m → List (Fin n)) (c : Fin n) : ℕ :=
  (Finset.univ.filter fun v => isTopOfList (ballots v) c).card

/-- Count voters who prefer `a` to `b`. -/
def countPrefers (ballots : Fin m → List (Fin n)) (a b : Fin n) : ℕ :=
  (Finset.univ.filter fun v => prefersInList (ballots v) a b).card

/-- Margin of `a` over `b`: voters preferring a minus voters preferring b. -/
def marginList (ballots : Fin m → List (Fin n)) (a b : Fin n) : ℤ :=
  (countPrefers ballots a b : ℤ) - (countPrefers ballots b a : ℤ)

end AggregateComputations

/-! ### Bridge Lemmas -/

section BridgeLemmas

variable {m n : ℕ}

/-- Prefers in a list-based profile corresponds to prefersInList. -/
lemma prefers_iff_prefersInList (ballots : Fin m → ListBallot n) (v : Fin m) (a b : Fin n) :
    Prefers (profileOfListBallots ballots) v a b ↔ prefersInList (ballots v).ranking a b = true := by
  unfold Prefers profileOfListBallots prefersInList
  simp only
  rw [(ballots v).lt_iff_idxOf]
  simp only [decide_eq_true_eq]

/-- Helper: the head of a nonempty list has idxOf 0. -/
lemma idxOf_head_eq_zero {α : Type*} [DecidableEq α] {l : List α} (h : l ≠ []) :
    l.idxOf (l.head h) = 0 := by
  cases l with
  | nil => contradiction
  | cons x xs => simp [List.idxOf_cons_self]

/-- TopRank in a list-based profile corresponds to isTopOfList on the ranking. -/
lemma topRank_iff_isTopOfList (ballots : Fin m → ListBallot n) (v : Fin m) (c : Fin n) :
    TopRank (profileOfListBallots ballots) v c ↔ isTopOfList (ballots v).ranking c = true := by
  constructor
  · intro htop
    unfold isTopOfList
    simp only [decide_eq_true_eq]
    -- c is preferred to all others, so it must be first
    by_cases hn : n = 0
    · exact Fin.elim0 (hn ▸ c)
    · have hne : (ballots v).ranking ≠ [] := by
        intro h
        have := (ballots v).perm.length_eq
        simp [h, List.length_finRange] at this
        omega
      rw [List.head?_eq_some_head hne]
      congr 1
      by_contra hne'
      have hidx_head : (ballots v).ranking.idxOf ((ballots v).ranking.head hne) = 0 :=
        idxOf_head_eq_zero hne
      have hc_mem := (ballots v).complete c
      have hhead_ne_c : (ballots v).ranking.head hne ≠ c := hne'
      have := htop ((ballots v).ranking.head hne) hhead_ne_c
      unfold Prefers profileOfListBallots at this
      simp only at this
      rw [(ballots v).lt_iff_idxOf] at this
      have hidx_c := List.idxOf_lt_length_of_mem hc_mem
      omega
  · intro htop
    unfold isTopOfList at htop
    simp only [decide_eq_true_eq] at htop
    intro d hd
    unfold Prefers profileOfListBallots
    simp only
    rw [(ballots v).lt_iff_idxOf]
    have hne : (ballots v).ranking ≠ [] := by
      intro h
      simp [h] at htop
    rw [List.head?_eq_some_head hne] at htop
    injection htop with hc_head
    have hidx_c : (ballots v).ranking.idxOf c = 0 := by
      rw [← hc_head]
      exact idxOf_head_eq_zero hne
    have hd_mem := (ballots v).complete d
    have hidx_d := List.idxOf_lt_length_of_mem hd_mem
    have hd_ne : (ballots v).ranking.idxOf d ≠ 0 := by
      intro h
      have heq : (ballots v).ranking.idxOf c = (ballots v).ranking.idxOf d := by omega
      exact hd ((List.idxOf_inj ((ballots v).complete c)).mp heq).symm
    omega

/-- votersTop in a list-based profile equals the filter by isTopOfList. -/
lemma votersTop_eq_filter_isTopOfList (ballots : Fin m → ListBallot n) (c : Fin n) :
    votersTop (profileOfListBallots ballots) c =
    Finset.univ.filter (fun v => isTopOfList (ballots v).ranking c) := by
  ext v
  simp only [votersTop, mem_filter, mem_univ, true_and]
  exact topRank_iff_isTopOfList ballots v c

/-- The cardinality of votersTop equals countTop. -/
lemma votersTop_card_eq_countTop (ballots : Fin m → ListBallot n) (c : Fin n) :
    (votersTop (profileOfListBallots ballots) c).card =
    countTop (fun v => (ballots v).ranking) c := by
  unfold countTop
  rw [votersTop_eq_filter_isTopOfList]

/-- votersPreferring in a list-based profile equals the filter by prefersInList. -/
lemma votersPreferring_eq_filter_prefersInList (ballots : Fin m → ListBallot n) (a b : Fin n) :
    votersPreferring (profileOfListBallots ballots) a b =
    Finset.univ.filter (fun v => prefersInList (ballots v).ranking a b) := by
  ext v
  simp only [votersPreferring, mem_filter, mem_univ, true_and]
  exact prefers_iff_prefersInList ballots v a b

/-- The margin in a list-based profile equals marginList. -/
lemma margin_eq_marginList (ballots : Fin m → ListBallot n) (a b : Fin n) :
    margin (profileOfListBallots ballots) a b =
    marginList (fun v => (ballots v).ranking) a b := by
  unfold margin marginList countPrefers
  have h1 : ∀ v, Prefers (profileOfListBallots ballots) v a b ↔
      prefersInList (ballots v).ranking a b = true :=
    fun v => prefers_iff_prefersInList ballots v a b
  have h2 : ∀ v, Prefers (profileOfListBallots ballots) v b a ↔
      prefersInList (ballots v).ranking b a = true :=
    fun v => prefers_iff_prefersInList ballots v b a
  simp only [h1, h2, Int.ofNat_eq_natCast]

/-- margin_pos in a list-based profile corresponds to positive marginList. -/
lemma margin_pos_iff_marginList_pos (ballots : Fin m → ListBallot n) (a b : Fin n) :
    margin_pos (profileOfListBallots ballots) a b ↔
    marginList (fun v => (ballots v).ranking) a b > 0 := by
  unfold margin_pos
  rw [margin_eq_marginList]

/-- condorcet_winner in a list-based profile. -/
lemma condorcet_winner_iff_marginList (ballots : Fin m → ListBallot n) (c : Fin n) :
    condorcet_winner (profileOfListBallots ballots) c ↔
    ∀ d : Fin n, c ≠ d → marginList (fun v => (ballots v).ranking) c d > 0 := by
  unfold condorcet_winner
  constructor
  · intro h d hne
    rw [← margin_pos_iff_marginList_pos]
    exact h d hne
  · intro h d hne
    rw [margin_pos_iff_marginList_pos]
    exact h d hne

end BridgeLemmas

/-! ### Example: 3-voter profile using ListBallot -/

namespace Examples

section ExampleProfile

/-- Three voters, three candidates. -/
abbrev V3 := Fin 3
abbrev A3 := Fin 3

/-- ListBallot for 0 > 1 > 2. -/
def listBallot012 : ListBallot 3 := ListBallot.identity 3

/-- ListBallot for 1 > 2 > 0. -/
def listBallot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]

/-- The ballots for our 3-voter example. -/
def exampleBallots : Fin 3 → ListBallot 3
  | 0 => listBallot012
  | 1 => listBallot012
  | 2 => listBallot120

/-- The example profile constructed from ListBallots. -/
noncomputable def exampleProfile : Profile V3 A3 :=
  profileOfListBallots exampleBallots

/-- Unfold exampleProfile to profileOfListBallots. -/
lemma exampleProfile_eq : exampleProfile = profileOfListBallots exampleBallots := rfl

/-! #### Computational proofs using the bridge lemmas -/

/-- Candidate 0 is on top for voters 0 and 1, verified computationally. -/
example : isTopOfList (exampleBallots 0).ranking 0 = true := rfl
example : isTopOfList (exampleBallots 1).ranking 0 = true := rfl
example : isTopOfList (exampleBallots 2).ranking 0 = false := rfl

/-- Count of voters with 0 on top, computed directly. -/
example : countTop (fun v => (exampleBallots v).ranking) 0 = 2 := rfl

/-- Voter 0 ranks candidate 0 on top (using bridge lemma). -/
lemma voter0_top0 : TopRank exampleProfile 0 0 := by
  rw [exampleProfile_eq, topRank_iff_isTopOfList]
  rfl

/-- Voter 1 ranks candidate 0 on top (using bridge lemma). -/
lemma voter1_top0 : TopRank exampleProfile 1 0 := by
  rw [exampleProfile_eq, topRank_iff_isTopOfList]
  rfl

/-- Voter 2 does NOT rank candidate 0 on top. -/
lemma voter2_not_top0 : ¬TopRank exampleProfile 2 0 := by
  rw [exampleProfile_eq, topRank_iff_isTopOfList]
  simp only [exampleBallots, listBallot120, ListBallot.mk', isTopOfList]
  decide

/-- There are exactly 2 voters who rank candidate 0 on top. -/
theorem two_voters_top0 : (votersTop exampleProfile 0).card = 2 := by
  rw [exampleProfile_eq, votersTop_card_eq_countTop]
  rfl

/-! #### Additional examples showing computational power -/

/-- Margins computed directly. -/
-- 0 vs 1: voters 0,1 prefer 0; voter 2 prefers 1 → margin = 2 - 1 = 1
example : marginList (fun v => (exampleBallots v).ranking) 0 1 = 1 := by rfl
-- 0 vs 2: voters 0,1 prefer 0; voter 2 prefers 2 → margin = 2 - 1 = 1
example : marginList (fun v => (exampleBallots v).ranking) 0 2 = 1 := by rfl
-- 1 vs 2: all 3 voters prefer 1 → margin = 3 - 0 = 3
example : marginList (fun v => (exampleBallots v).ranking) 1 2 = 3 := by rfl

/-- Preference checks. -/
example : prefersInList (exampleBallots 0).ranking 0 1 = true := rfl
example : prefersInList (exampleBallots 2).ranking 1 0 = true := rfl

end ExampleProfile

/-! ### Example: 4-candidate Condorcet winner -/

section CondorcetExample

/--
A 3-voter, 4-candidate profile where 0 is the Condorcet winner:
- Voter 0: 3 > 0 > 2 > 1  (ranking: [3, 0, 2, 1])
- Voter 1: 0 > 1 > 3 > 2  (ranking: [0, 1, 3, 2])
- Voter 2: 1 > 2 > 0 > 3  (ranking: [1, 2, 0, 3])

Candidate 0 beats all others:
- 0 vs 1: voters 0,1 prefer 0; voter 2 prefers 1 → margin = 1
- 0 vs 2: voters 0,1 prefer 0; voter 2 prefers 2 → margin = 1
- 0 vs 3: voters 1,2 prefer 0; voter 0 prefers 3 → margin = 1
-/

def condorcetBallots : Fin 3 → ListBallot 4
  | 0 => ListBallot.mk' [3, 0, 2, 1]
  | 1 => ListBallot.mk' [0, 1, 3, 2]
  | 2 => ListBallot.mk' [1, 2, 0, 3]

noncomputable def condorcetProfile : Profile (Fin 3) (Fin 4) :=
  profileOfListBallots condorcetBallots

lemma condorcetProfile_eq : condorcetProfile = profileOfListBallots condorcetBallots := rfl

/-! #### Computational verification of margins -/

-- All margins involving candidate 0:
example : marginList (fun v => (condorcetBallots v).ranking) 0 1 = 1 := rfl
example : marginList (fun v => (condorcetBallots v).ranking) 0 2 = 1 := rfl
example : marginList (fun v => (condorcetBallots v).ranking) 0 3 = 1 := rfl

-- Candidate 0 has positive margin against all others (computational check)
example : marginList (fun v => (condorcetBallots v).ranking) 0 1 > 0 := by decide
example : marginList (fun v => (condorcetBallots v).ranking) 0 2 > 0 := by decide
example : marginList (fun v => (condorcetBallots v).ranking) 0 3 > 0 := by decide

/-! #### Proof that 0 is Condorcet winner (abstract definition) -/

/-- Candidate 0 is the Condorcet winner in the list-based sense. -/
theorem zero_is_condorcet_winner_list :
    ∀ d : Fin 4, (0 : Fin 4) ≠ d →
      marginList (fun v => (condorcetBallots v).ranking) 0 d > 0 := by
  intro d hne
  fin_cases d
  · simp at hne
  · decide
  · decide
  · decide

/-- Candidate 0 is the Condorcet winner in the abstract sense (from Condorcet.lean). -/
theorem zero_is_condorcet_winner :
    condorcet_winner condorcetProfile (0 : Fin 4) := by
  rw [condorcetProfile_eq, condorcet_winner_iff_marginList]
  exact zero_is_condorcet_winner_list

end CondorcetExample

end Examples

end SocialChoice
