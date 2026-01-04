import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import SocialChoice.Profile

namespace SocialChoice

open Finset

/--
`rank r c` is the number of candidates strictly above `c` in the linear order `r`.
We define a 1-based `position` as `rank + 1`.
-/
def rank {A : Type} [Fintype A] (r : LinearOrder A) (c : A) : Nat :=
  (Finset.univ.filter (fun d => r.lt d c)).card

def position {A : Type} [Fintype A] (r : LinearOrder A) (c : A) : Nat :=
  rank r c + 1

theorem position_eq_rank_succ {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    position r c = rank r c + 1 := rfl

theorem rank_le_card {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    rank r c ≤ Fintype.card A := by
  classical
  change (Finset.univ.filter (fun d => r.lt d c)).card ≤ (Finset.univ : Finset A).card
  exact
    Finset.card_le_card
      (Finset.filter_subset (s := (Finset.univ : Finset A)) (p := fun d => r.lt d c))

theorem rank_lt_card {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    rank r c < Fintype.card A := by
  classical
  change (Finset.univ.filter (fun d => r.lt d c)).card < (Finset.univ : Finset A).card
  have hsubset :
      (Finset.univ.filter (fun d => r.lt d c)) ⊂ (Finset.univ : Finset A) := by
    refine (Finset.ssubset_iff_of_subset
      (Finset.filter_subset (s := (Finset.univ : Finset A)) (p := fun d => r.lt d c))).2 ?_
    refine ⟨c, by simp, ?_⟩
    simp
  exact Finset.card_lt_card hsubset

lemma rank_lt_of_lt {A : Type} [Fintype A] (r : LinearOrder A) {c d : A} (hcd : r.lt c d) :
    rank r c < rank r d := by
  classical
  let _ := r
  have hsubset :
      (Finset.univ.filter (fun a : A => a < c)) ⊆
        (Finset.univ.filter (fun a : A => a < d)) := by
    intro a ha
    have ha' : a < c := (Finset.mem_filter.mp ha).2
    have had : a < d := lt_trans ha' hcd
    exact Finset.mem_filter.mpr ⟨by simp, had⟩
  have hssub :
      (Finset.univ.filter (fun a : A => a < c)) ⊂
        (Finset.univ.filter (fun a : A => a < d)) := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    refine ⟨c, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, hcd⟩
    · intro hc
      have hc' : c < c := (Finset.mem_filter.mp hc).2
      exact (lt_irrefl _ hc')
  simpa [rank] using (Finset.card_lt_card hssub)

theorem position_le_card {A : Type} [Fintype A] (r : LinearOrder A) (c : A) :
    position r c ≤ Fintype.card A := by
  have h := rank_lt_card r c
  simpa [position, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt h)

end SocialChoice
