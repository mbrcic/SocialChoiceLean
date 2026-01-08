import SocialChoice.Axioms.Strategyproofness
import SocialChoice.Rank

namespace SocialChoice

/-!
# Down-Monotonicity for Singleton Winners

This file defines down-monotonicity for singleton winners and proves that
optimist and pessimist strategyproofness together imply this property.

This is Lemma 2.4 from Taylor's "The Manipulability of Voting Systems" (2002),
which is a key step in the proof of the Duggan-Schwartz theorem.

## Main Definitions

* `swapInBallot`: Swapping two alternatives on a ballot
* `swapInProfile`: Swapping two alternatives in a voter's ballot within a profile
* `DownMonotonicitySingleton`: The down-monotonicity property for singleton winners

## Main Results

* `downMonotonicity_of_opt_pess_sp`: Optimist + pessimist strategyproofness
  implies down-monotonicity for singleton winners.
-/

open Finset

variable {V A : Type} [Fintype V] [Fintype A]

/-! ## Ballot Manipulation: Swapping Alternatives -/

/-- Swap two alternatives in a linear order.
    The resulting order has x and y swapped: (swap r x y).lt a b ↔ r.lt (swap a) (swap b). -/
noncomputable def swapInBallot (r : LinearOrder A) (x y : A) : LinearOrder A := by
  classical
  exact relabelBallot r (Equiv.swap x y)

/-- A profile where one voter has two alternatives swapped on their ballot. -/
noncomputable def swapInProfile (P : Profile V A) (v : V) (x y : A) : Profile V A :=
  updateProfile P v (swapInBallot (P.pref v) x y)

/-! ## Properties of Ballot Swapping -/

/-- The fundamental property of swapInBallot. -/
lemma swapInBallot_lt (r : LinearOrder A) (x y a b : A) :
    (swapInBallot r x y).lt a b ↔ r.lt (Equiv.swap x y a) (Equiv.swap x y b) := by
  unfold swapInBallot relabelBallot
  simp only [LinearOrder.lift'_lt]

/-- Swapping x and y reverses their relative order. -/
lemma swapInBallot_swap (r : LinearOrder A) (x y : A) :
    (swapInBallot r x y).lt x y ↔ r.lt y x := by
  rw [swapInBallot_lt]
  simp

/-- Swapping x and y reverses their relative order (symmetric version). -/
lemma swapInBallot_swap' (r : LinearOrder A) (x y : A) :
    (swapInBallot r x y).lt y x ↔ r.lt x y := by
  rw [swapInBallot_lt]
  simp

/-- Swapping preserves relative order of alternatives not in {x, y}. -/
lemma swapInBallot_preserves (r : LinearOrder A) (x y a b : A)
    (ha : a ≠ x) (ha' : a ≠ y) (hb : b ≠ x) (hb' : b ≠ y) :
    (swapInBallot r x y).lt a b ↔ r.lt a b := by
  rw [swapInBallot_lt]
  simp [Equiv.swap_apply_of_ne_of_ne ha ha', Equiv.swap_apply_of_ne_of_ne hb hb']

/-- Swapping twice returns the original order. -/
lemma swapInBallot_swapInBallot (r : LinearOrder A) (x y : A) :
    swapInBallot (swapInBallot r x y) x y = r := by
  ext a b
  simp only [swapInBallot_lt, Equiv.swap_apply_self]

/-- The original profile P equals an update of the swapped profile. -/
lemma profile_eq_update_of_swap (P : Profile V A) (v : V) (x y : A) :
    P = updateProfile (swapInProfile P v x y) v (P.pref v) := by
  ext u
  unfold swapInProfile updateProfile
  simp only
  by_cases huv : u = v <;> simp [huv]

/-- swapInProfile relates to updateProfile. -/
lemma swapInProfile_eq (P : Profile V A) (v : V) (x y : A) :
    swapInProfile P v x y = updateProfile P v (swapInBallot (P.pref v) x y) := rfl

/-! ## Adjacency -/

/-- Two alternatives x and y are adjacent in a linear order if x is immediately
    above y (i.e., x < y and there's no z with x < z < y). -/
def Adjacent (r : LinearOrder A) (x y : A) : Prop :=
  r.lt x y ∧ ∀ z : A, ¬(r.lt x z ∧ r.lt z y)

/-- If x and y are adjacent, the only pair whose relative order changes is {x, y}. -/
lemma swap_adjacent_only_changes_xy (r : LinearOrder A) (x y : A) (hadj : Adjacent r x y)
    (a b : A) (hab : a ≠ b) :
    ((swapInBallot r x y).lt a b ↔ r.lt a b) ∨ ({a, b} = ({x, y} : Set A)) := by
  by_cases hax : a = x
  · by_cases hbx : b = x
    · exact absurd (hbx.trans hax.symm) hab
    · by_cases hby : b = y
      · right; subst hax hby; ext c; simp [Set.mem_insert_iff]
      · -- a = x, b ∉ {x, y}
        left
        rw [swapInBallot_lt]
        simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbx hby]
        -- (swap).lt x b ↔ r.lt y b
        -- Need to show: r.lt y b ↔ r.lt x b
        constructor
        · intro hyb
          -- y < b and x < y (from hadj), so x < b
          exact lt_trans hadj.1 hyb
        · intro hxb
          -- x < b. Is y < b?
          -- Since x and y are adjacent, either b ≤ x, x < b ≤ y, or y < b
          -- We have x < b, so not b ≤ x
          -- If x < b ≤ y, then x < b and b ≤ y, so b < y or b = y
          -- If b < y, then x < b < y contradicts adjacency
          -- If b = y, then b = y contradicts hby
          -- So we must have y < b
          by_contra hyb
          have hby' : r.le b y := le_of_not_lt hyb
          rcases lt_or_eq_of_le hby' with hby'' | hbeqy
          · exact hadj.2 b ⟨hxb, hby''⟩
          · exact hby hbeqy.symm
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · right; subst hay hbx; ext c; simp [Set.mem_insert_iff, Set.insert_comm]
      · by_cases hby : b = y
        · exact absurd (hby.trans hay.symm) hab
        · -- a = y, b ∉ {x, y}
          left
          rw [swapInBallot_lt]
          simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbx hby]
          -- (swap).lt y b ↔ r.lt x b
          -- Need to show: r.lt x b ↔ r.lt y b
          constructor
          · intro hxb
            -- x < b. Need y < b.
            by_contra hyb
            have hby' : r.le b y := le_of_not_lt hyb
            rcases lt_or_eq_of_le hby' with hby'' | hbeqy
            · exact hadj.2 b ⟨hxb, hby''⟩
            · exact hby hbeqy.symm
          · intro hyb
            exact lt_trans hadj.1 hyb
    · -- a ∉ {x, y}
      by_cases hbx : b = x
      · -- b = x, a ∉ {x, y}
        left
        rw [swapInBallot_lt]
        simp only [Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_left]
        -- (swap).lt a x ↔ r.lt a y
        -- Need: r.lt a y ↔ r.lt a x
        constructor
        · intro hay'
          -- a < y. Need a < x.
          -- Either a < x or x ≤ a
          by_contra hax'
          have hxa : r.le x a := le_of_not_lt hax'
          rcases lt_or_eq_of_le hxa with hxa' | hxeqa
          · -- x < a < y contradicts adjacency
            exact hadj.2 a ⟨hxa', hay'⟩
          · exact hax hxeqa
        · intro hax'
          -- a < x < y, so a < y
          exact lt_trans hax' hadj.1
      · by_cases hby : b = y
        · -- b = y, a ∉ {x, y}
          left
          rw [swapInBallot_lt]
          simp only [Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_right]
          -- (swap).lt a y ↔ r.lt a x
          -- Need: r.lt a x ↔ r.lt a y
          constructor
          · intro hax'
            exact lt_trans hax' hadj.1
          · intro hay'
            by_contra hax'
            have hxa : r.le x a := le_of_not_lt hax'
            rcases lt_or_eq_of_le hxa with hxa' | hxeqa
            · exact hadj.2 a ⟨hxa', hay'⟩
            · exact hax hxeqa
        · -- a ∉ {x, y}, b ∉ {x, y}
          left
          exact swapInBallot_preserves r x y a b hax hay hbx hby

/-! ## Down-Monotonicity for Singleton Winners -/

/-- Down-monotonicity for singleton winners: if f(P) = {w} (a singleton),
    and P' is obtained from P by having one voter swap two ADJACENT alternatives
    x and y on their ballot where x is a loser (x ≠ w) and x is immediately above y,
    then f(P') = {w}.

    This is Definition 2.3 from Taylor (2002). The adjacency condition is crucial:
    "move one losing alternative down one spot" means swapping with the immediately
    below alternative. -/
def DownMonotonicitySingleton (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (w x y : A),
    f P = {w} →
    x ≠ w →  -- x is a loser
    Adjacent (P.pref v) x y →  -- x is immediately above y
    f (swapInProfile P v x y) = {w}

/-! ## Main Theorem -/

/-- Lemma 2.4 from Taylor (2002): If a voting system cannot be manipulated by
    an optimist or a pessimist, then it satisfies down-monotonicity for
    singleton winners.

    Proof: Suppose down-monotonicity fails. Then swapping adjacent x and y
    (where x is a loser immediately above y) changes the outcome from {w}
    to some Y ≠ {w}. Pick v' ∈ Y with v' ≠ w.

    Since x and y are adjacent, the only pair whose relative order changes
    is {x, y} itself. So if v' and w have the same relative order in both
    ballots, we get a manipulation. If their order differs, then {v', w} = {x, y}.

    Case 1: v' is preferred to w in BOTH ballots → optimist manipulation.
    Case 2: w is preferred to v' in BOTH ballots → pessimist manipulation.
    Case 3: {v', w} = {x, y}. Since w ≠ x (loser), we have w = y and v' = x.
            In original ballot, x > y means v' > w → optimist manipulation. -/
theorem downMonotonicity_of_opt_pess_sp (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f) :
    DownMonotonicitySingleton f := by
  intro V A _ _ P v w x y hfP hxw hadj
  by_contra hne
  let P' := swapInProfile P v x y
  let r := P.pref v

  -- Extract x < y from adjacency
  have hxy : r.lt x y := hadj.1

  -- f(P') is nonempty and differs from {w}, so find v' ∈ f(P') with v' ≠ w
  have hnonempty : (f P').Nonempty := hf_total P'
  have hex_ne : ∃ v' ∈ f P', v' ≠ w := by
    by_cases hw_mem : w ∈ f P'
    · have hcard_ne : (f P').card ≠ 1 := fun hc => by
        rw [Finset.card_eq_one] at hc
        obtain ⟨z, hz⟩ := hc
        have : w = z := by simpa using (hz ▸ hw_mem : w ∈ ({z} : Finset A))
        exact hne (this ▸ hz)
      have hcard_pos : 0 < (f P').card := Finset.card_pos.mpr ⟨w, hw_mem⟩
      have hcard_gt1 : 1 < (f P').card := Nat.lt_of_le_of_ne
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)) (Ne.symm hcard_ne)
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard_gt1
      exact if haw : a = w then ⟨b, hb, fun hbw => hab (haw.trans hbw.symm)⟩ else ⟨a, ha, haw⟩
    · obtain ⟨v', hv'⟩ := hnonempty
      exact ⟨v', hv', fun h => hw_mem (h ▸ hv')⟩

  obtain ⟨v', hv'mem, hv'w⟩ := hex_ne

  let r' := (swapInProfile P v x y).pref v
  have hr' : r' = swapInBallot r x y := by simp [r', swapInProfile, updateProfile]

  -- Key lemma: since x and y are adjacent, order changes only for {x, y}
  have horder_preserved : ∀ a b : A, a ≠ b →
      ((swapInBallot r x y).lt a b ↔ r.lt a b) ∨ ({a, b} = ({x, y} : Set A)) :=
    swap_adjacent_only_changes_xy r x y hadj

  -- Case analysis on relative order of v' and w
  rcases lt_trichotomy (r.toPartialOrder.toPreorder.toLT.lt v' w) with hvw_lt | hvw_eq | hwv_lt

  · -- Case: v' < w in r (v' preferred to w)
    rcases horder_preserved v' w hv'w with hpres | hxy_eq
    · -- Order preserved: v' < w in both r and r'
      have hvw'_lt : r'.lt v' w := by rw [hr']; exact hpres.mpr hvw_lt
      have hmanip : ∃ y' ∈ f P', ∀ x' ∈ f P, Prefers P v y' x' := by
        refine ⟨v', hv'mem, fun x' hx' => ?_⟩
        simp only [hfP, mem_singleton] at hx'; subst hx'; exact hvw_lt
      have hP'_eq : P' = updateProfile P v (P'.pref v) := by
        ext u; simp [swapInProfile, updateProfile]; by_cases h : u = v <;> simp [h]
      rw [hP'_eq] at hmanip
      exact hf_opt P v (P'.pref v) hmanip
    · -- {v', w} = {x, y}
      -- Since w ≠ x (hxw), we have either v' = x, w = y or v' = y, w = x
      have hv'w_in : v' ∈ ({x, y} : Set A) ∧ w ∈ ({x, y} : Set A) := by
        constructor
        · have : v' ∈ ({v', w} : Set A) := by simp
          rw [hxy_eq] at this; exact this
        · have : w ∈ ({v', w} : Set A) := by simp
          rw [hxy_eq] at this; exact this
      rcases hv'w_in.1 with hv'x | hv'y <;> rcases hv'w_in.2 with hwx | hwy
      · exact absurd (hv'x.trans hwx.symm) hv'w
      · -- v' = x, w = y: matches hxy, use optimist manipulation
        subst hv'x hwy
        have hmanip : ∃ y' ∈ f P', ∀ x' ∈ f P, Prefers P v y' x' := by
          refine ⟨x, hv'mem, fun x' hx' => ?_⟩
          simp only [hfP, mem_singleton] at hx'; subst hx'; exact hxy
        have hP'_eq : P' = updateProfile P v (P'.pref v) := by
          ext u; simp [swapInProfile, updateProfile]; by_cases h : u = v <;> simp [h]
        rw [hP'_eq] at hmanip
        exact hf_opt P v (P'.pref v) hmanip
      · exact absurd hwx hxw
      · exact absurd (hv'y.trans hwy.symm) hv'w

  · exact absurd hvw_eq hv'w

  · -- Case: w < v' in r (w preferred to v')
    rcases horder_preserved w v' (Ne.symm hv'w) with hpres | hxy_eq
    · -- Order preserved: w < v' in both r and r'
      have hwv'_lt : r'.lt w v' := by rw [hr']; exact hpres.mpr hwv_lt
      have hmanip : ∃ x' ∈ f P', ∀ y' ∈ f (updateProfile P' v (P.pref v)), Prefers P' v y' x' := by
        refine ⟨v', hv'mem, fun y' hy' => ?_⟩
        have hP_eq : updateProfile P' v (P.pref v) = P := by
          rw [← profile_eq_update_of_swap P v x y]
        rw [hP_eq] at hy'
        simp only [hfP, mem_singleton] at hy'; subst hy'
        unfold Prefers; simp [swapInProfile, updateProfile]; exact hwv'_lt
      exact hf_pess P' v (P.pref v) hmanip
    · -- {w, v'} = {x, y}
      have hwv'_in : w ∈ ({x, y} : Set A) ∧ v' ∈ ({x, y} : Set A) := by
        constructor
        · have : w ∈ ({w, v'} : Set A) := by simp
          rw [hxy_eq] at this; exact this
        · have : v' ∈ ({w, v'} : Set A) := by simp
          rw [hxy_eq] at this; exact this
      rcases hwv'_in.1 with hwx | hwy <;> rcases hwv'_in.2 with hv'x | hv'y
      · exact absurd hwx hxw
      · -- w = x, v' = y: but hwv_lt says x < y which contradicts hxy (x < y means x preferred)
        subst hwx hv'y
        -- hwv_lt: r.lt w v' = r.lt x y, which is exactly hxy. No contradiction!
        -- Actually we have w < v' meaning w preferred, but w = x and v' = y
        -- so x < y means x preferred. But wait, hwv_lt says r.lt w v' = r.lt x y
        -- That's the same as hxy! So x is preferred to y.
        -- Optimist manipulation: with P as true, v' = y is worse than w = x
        -- But v' = y is in f(P'), and w = x is in f(P) = {x}. Wait, w = x?
        -- No, we have w ≠ x from hxw! So w = x is impossible.
        exact absurd hwx hxw
      · exact absurd (hwx.trans hv'x.symm) (Ne.symm hv'w)
      · exact absurd (hwy.trans hv'y.symm) (Ne.symm hv'w)

end SocialChoice
