import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Axioms.Condorcet

namespace SocialChoice

open Finset
open scoped BigOperators

/-!
# IRV Satisfies the Condorcet Loser Criterion

This file proves that Instant Runoff Voting (IRV) satisfies the Condorcet loser criterion:
a Condorcet loser (a candidate who loses pairwise to every other candidate) cannot win.

## Proof sketch

Suppose `d` is a Condorcet loser and assume for contradiction that `d` wins IRV.
Then at some point during elimination, there exists a two-candidate set `{c, d}`
where `c` is eliminated (has lower plurality score) and `d` survives to win.

But in a two-candidate race:
- The plurality score of a candidate = number of first-place votes
- Number of first-place votes = number preferring you (since there are only 2)

Since `d` is a Condorcet loser, more voters prefer `c` to `d` than prefer `d` to `c`.
Therefore `c` has higher plurality score, contradicting that `c` was eliminated.
-/

variable {V A : Type} [Fintype V] [Fintype A]

/-! ### Two-candidate election lemmas -/

/-- In a two-candidate election, TopRank is equivalent to pairwise preference -/
lemma topRank_iff_prefers_of_two (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (v : V) :
    TopRank P v c ↔ Prefers P v c d := by
  constructor
  · intro htop
    exact htop d hcd.symm
  · intro hpref e he
    rcases two_elems_eq_or_eq hcard c d hcd e with rfl | rfl
    · exact (he rfl).elim
    · exact hpref

/-- In a two-candidate election, the number of top-ranks equals
    the number of voters who prefer that candidate -/
lemma votersTop_eq_votersPreferring_of_two (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) :
    votersTop P c = votersPreferring P c d := by
  classical
  ext v
  simp only [votersTop, votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  exact topRank_iff_prefers_of_two P hcard c d hcd v

/-- Plurality score equals cards of votersTop -/
lemma pluralityScore_eq_votersTop_card (P : Profile V A) (c : A) :
    scoreCandidate P (fun r => if r = 0 then 1 else 0) c =
      (votersTop P c).card := by
  classical
  -- rank = 0 iff TopRank
  have hrankTop : ∀ v, rank (P.pref v) c = 0 ↔ TopRank P v c := by
    intro v
    constructor
    · intro hr d hd
      -- rank c = 0 means no one is above c
      unfold rank at hr
      have hempty : (Finset.univ.filter (fun x => (P.pref v).lt x c)) = ∅ := by
        exact Finset.card_eq_zero.mp hr
      have hd_not_above : d ∉ Finset.univ.filter (fun x => (P.pref v).lt x c) := by
        simp [hempty]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd_not_above
      -- d is not above c, and d ≠ c, so c < d
      let _ := P.pref v
      have hord : c < d ∨ d < c := lt_or_gt_of_ne (Ne.symm hd)
      cases hord with
      | inl hlt => exact hlt
      | inr hgt => exact (hd_not_above hgt).elim
    · intro htop
      unfold rank
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hdlt : (P.pref v).lt d c := (Finset.mem_filter.mp hd).2
      have hdc : d ≠ c := by
        intro heq; subst heq
        let _ := P.pref v
        exact lt_irrefl _ hdlt
      have hcd : (P.pref v).lt c d := htop d hdc
      let _ := P.pref v
      exact lt_asymm hcd hdlt
  -- Rewrite to use TopRank instead of rank = 0
  have heq : (∑ v : V, (fun r => if r = 0 then (1 : Int) else 0) (rank (P.pref v) c)) =
             ∑ v : V, if TopRank P v c then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    simp only [hrankTop v]
  have hsum :
      (∑ v : V, if TopRank P v c then (1 : Int) else 0) =
    ((Finset.univ.filter (fun v => TopRank P v c)).card : Int) := by
    classical
    have hsum_univ :
        (∑ v : V, if TopRank P v c then (1 : Int) else 0) =
          (Finset.univ : Finset V).sum (fun v => if TopRank P v c then (1 : Int) else 0) := by
      simp
    have hsum_filtered :
        ((Finset.univ : Finset V).sum (fun v => if TopRank P v c then (1 : Int) else 0)) =
          (Finset.univ.filter (fun v => TopRank P v c)).sum (fun _ => (1 : Int)) := by
      have h := (Finset.sum_filter
        (s := (Finset.univ : Finset V))
        (p := fun v => TopRank P v c)
        (f := fun _ => (1 : Int)))
      exact h.symm
    have hsum_card :
        ((Finset.univ.filter (fun v => TopRank P v c)).sum (fun _ => (1 : Int))) =
          ((Finset.univ.filter (fun v => TopRank P v c)).card : Int) := by
      simp
    exact hsum_univ.trans (hsum_filtered.trans hsum_card)
  have hscore : scoreCandidate P (fun r => if r = 0 then 1 else 0) c =
      ∑ v : V, if TopRank P v c then (1 : Int) else 0 := by
    simpa [scoreCandidate] using heq
  calc
    scoreCandidate P (fun r => if r = 0 then 1 else 0) c
        = ∑ v : V, if TopRank P v c then (1 : Int) else 0 := hscore
    _ = ((Finset.univ.filter fun v => TopRank P v c).card : Int) := hsum
    _ = (votersTop P c).card := by
            simp [votersTop]

/-- In two candidates, plurality score = number preferring you to the other -/
lemma pluralityScore_eq_votersPreferring_of_two (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) :
    scoreCandidate P (fun r => if r = 0 then 1 else 0) c =
      (votersPreferring P c d).card := by
  rw [pluralityScore_eq_votersTop_card, votersTop_eq_votersPreferring_of_two P hcard c d hcd]

/-! ### Condorcet loser in two-candidate election -/

/-- A Condorcet loser in a 2-candidate election has strictly fewer first-place votes -/
lemma CondorcetLoser_lower_plurality_two (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (hloser : CondorcetLoser P d) :
    scoreCandidate P (fun r => if r = 0 then 1 else 0) d <
      scoreCandidate P (fun r => if r = 0 then 1 else 0) c := by
  rw [pluralityScore_eq_votersPreferring_of_two P hcard d c (Ne.symm hcd)]
  rw [pluralityScore_eq_votersPreferring_of_two P hcard c d hcd]
  -- hloser says margin_pos P c d (since c ≠ d and d is Condorcet loser)
  have hmargin : margin_pos P c d :=
    (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := c) (d := d) (hcd := hcd)).1 (hloser.1 c hcd)
  -- margin_pos means more prefer c > d than d > c
  dsimp [margin_pos, margin] at hmargin
  have hmargin' :
      0 < Int.ofNat (votersPreferring P c d).card -
          Int.ofNat (votersPreferring P d c).card := by
    simpa [votersPreferring, Prefers] using hmargin
  -- The margin inequality rearranges to the desired comparison of counts.
  have hlt :
      (Int.ofNat (votersPreferring P d c).card) <
        Int.ofNat (votersPreferring P c d).card := sub_pos.mp hmargin'
  simpa using hlt

/-! ### Main theorem -/

theorem irv_CondorcetLoser_criterion : CondorcetLoserCriterion instantRunoffVoting := by
  intro V A _ _ P d hloser
  classical
  letI : DecidableEq A := Classical.decEq A
  -- Reduce to the auxiliary elimination function.
  change d ∉ scoringEliminationAux pluralityScore A P
  -- Strong induction on the number of candidates.
  set n : Nat := Fintype.card A
  have aux :
      ∀ n : Nat,
        (∀ m < n,
          ∀ {A : Type} [Fintype A] [DecidableEq A],
            Fintype.card A = m →
              ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
                CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P) →
        ∀ {A : Type} [Fintype A] [DecidableEq A],
          Fintype.card A = n →
            ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
              CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P := by
    intro n ih A _ _ hcard V _ P d hloser
    classical
    -- We are never in the base case `card ≤ 1`, since a Condorcet loser requires another candidate.
    have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
      intro hle
      have hsubs : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      rcases hloser.2 with ⟨y, hy⟩
      exact hy (Subsingleton.elim y d)
    -- Split on candidate count.
    by_cases htwo : Fintype.card A = 2
    · -- Two-candidate case: the Condorcet loser has strictly lower plurality score,
      -- hence cannot be the survivor in the unique elimination step.
      -- Unfold the elimination step.
      have hcard' : ¬ Fintype.card A ≤ 1 := hnot_le_one
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := P) (hcard := hcard')
      -- Now argue by contradiction from membership.
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      -- `d` is in the biUnion, so it survives some elimination of a lowest-scoring candidate `c`.
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      -- In a two-candidate election, `d` has strictly lower plurality score than `c`.
      have hlt :
          scoreCandidate P (fun r => pluralityScore 2 r) d <
            scoreCandidate P (fun r => pluralityScore 2 r) c := by
        -- `pluralityScore 2` is the usual plurality scoring vector.
        simpa [pluralityScore] using
          (CondorcetLoser_lower_plurality_two (V := V) (A := A) (P := P) (hcard := htwo)
            (c := c) (d := d) (hcd := hcd) (hloser := hloser))
      -- But `c` is lowest-scoring, so its score is ≤ `d`'s score.
      have hle :
          scoreCandidate P (fun r => pluralityScore 2 r) c ≤
            scoreCandidate P (fun r => pluralityScore 2 r) d :=
        scoreCandidate_le_of_mem_lowestScoring (P := P)
          (score := fun r => pluralityScore 2 r) (c := c) (e := d) hcL
      exact (not_lt_of_ge hle) hlt
    · -- Recursive case: at least three candidates.
      have hgt2 : 2 < Fintype.card A := by
        have hne2 : Fintype.card A ≠ 2 := htwo
        have hone : 1 < Fintype.card A := Nat.lt_of_not_ge hnot_le_one
        -- Now exclude `card = 2` to get `2 < card`.
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hone) (Ne.symm hne2)
      have hcard' : ¬ Fintype.card A ≤ 1 := hnot_le_one
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := P) (hcard := hcard')
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      have hdc : d ≠ c := by simpa [eq_comm] using hcd
      -- Convert `d ∈ liftFinset ...` into membership of the corresponding subtype element.
      have hd_in' : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∈
          scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c) := by
        -- `liftFinset` is `image Subtype.val`.
        have himage : d ∈ (scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c)).image
            (fun x : {x : A // x ≠ c} => (x : A)) := by
          simpa [liftFinset] using hd_in
        rcases Finset.mem_image.mp himage with ⟨x, hx, hxval⟩
        have hx' : x = (⟨d, hdc⟩ : {x : A // x ≠ c}) := by
          ext
          simpa using hxval
        simpa [hx'] using hx
      -- Apply the induction hypothesis to the restricted election.
      have hltcard : Fintype.card {x : A // x ≠ c} < n := by
        -- Use the strict decrease proved in `ScoringElimination/Defs.lean`.
        simpa [hcard] using (card_restrict_lt (A := A) c)
      have hloser' :
          CondorcetLoser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) :=
        CondorcetLoser_restrictProfile_of_two_lt_card (P := P) (hdc := hdc) (hcard := hgt2) hloser
      have hnot : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∉
          scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c) := by
        -- Specialize IH to the restricted type.
        have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
          (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
          (d := (⟨d, hdc⟩ : {x : A // x ≠ c})) hloser'
        simpa using this
      exact hnot hd_in'
  -- Finish by invoking `aux` at `n = card A`.
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
          CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    -- Build the IH required by `aux` from the `strongRecOn` hypothesis `ih`.
    intro A _ _ hcardA V _ P d hloser
    have ihAux :
        ∀ m < k,
          ∀ {A : Type} [Fintype A] [DecidableEq A],
            Fintype.card A = m →
              ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
                CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P := by
      intro m hm A _ _ hcardm V _ P d hloser
      -- `ih m hm` is the induction hypothesis at `m`.
      exact (ih m hm) (by simpa using hcardm) (P := P) (d := d) hloser
    exact aux k ihAux (A := A) (by simpa using hcardA) (V := V) (P := P) (d := d) hloser
  have := hStrong (A := A) (by rfl) (V := V) (P := P) (d := d) hloser
  simpa [Motive, n] using this

end SocialChoice
