import SocialChoice.Profile
import SocialChoice.ListBallot
import SocialChoice.Margin
import SocialChoice.Axioms.Condorcet
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

namespace SocialChoice

open Finset

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
theorem zero_is_CondorcetWinner_list :
    ∀ d : Fin 4, (0 : Fin 4) ≠ d →
      marginList (fun v => (condorcetBallots v).ranking) 0 d > 0 := by
  intro d hne
  fin_cases d
  · simp at hne
  · decide
  · decide
  · decide

/-- Candidate 0 is the Condorcet winner in the abstract sense (from Condorcet.lean). -/
theorem zero_is_CondorcetWinner :
    CondorcetWinner condorcetProfile (0 : Fin 4) := by
  rw [condorcetProfile_eq, CondorcetWinner_iff_marginList]
  exact zero_is_CondorcetWinner_list

end CondorcetExample

end Examples

end SocialChoice
