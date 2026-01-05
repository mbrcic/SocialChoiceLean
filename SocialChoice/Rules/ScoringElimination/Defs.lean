import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Function.Iterate
import SocialChoice.Rank
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

/-!
# Scoring Elimination Rules

This file defines scoring elimination rules (also known as iterated scoring rules).

The elimination scoring rule associated with a scoring system `s` selects a winning candidate
by repeatedly removing a candidate with the lowest s-score from the profile, until only one
candidate remains, who is the winner.

When there are ties for the lowest score, we use parallel-universe tie-breaking: we recursively
explore all branches by removing each lowest-scoring candidate, and take the union of all
resulting winners.

## Main definitions

* `lowestScoring`: The set of candidates with the minimum score in a profile.
* `scoringEliminationAux`: Auxiliary function implementing the elimination procedure.
* `scoringEliminationRule`: The main voting rule.
-/

-- Helper instance for restricted candidate types
noncomputable instance instFintypeNeq {A : Type} [Fintype A] [DecidableEq A] (c : A) :
    Fintype {x : A // x ≠ c} := by
  classical
  infer_instance

-- Restrict a profile by removing one candidate
noncomputable def restrictProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A) : Profile V {x : A // x ≠ c} :=
  restrictCandidates P (fun x => x ≠ c)

-- Compute the set of lowest-scoring candidates
noncomputable def lowestScoring {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) : Finset A := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let minScore : Int :=
      (Finset.univ.image (fun c => scoreCandidate P score c)).min' (by
        simpa [Finset.Nonempty] using h)
    exact (Finset.univ.filter (fun c => scoreCandidate P score c = minScore))
  · exact ∅

lemma lowestScoring_nonempty {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int) (hA : (Finset.univ : Finset A).Nonempty) :
    (lowestScoring P score).Nonempty := by
  classical
  simp only [lowestScoring, hA, dite_true]
  let scoreSet := Finset.univ.image (fun c => scoreCandidate P score c)
  have hScoreNonempty : scoreSet.Nonempty := by
    simpa [scoreSet, Finset.Nonempty] using hA.image (fun c => scoreCandidate P score c)
  let minScore := scoreSet.min' hScoreNonempty
  have hMinMem : minScore ∈ scoreSet := Finset.min'_mem scoreSet hScoreNonempty
  rcases Finset.mem_image.mp hMinMem with ⟨c, _, hc⟩
  refine ⟨c, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- hc : scoreCandidate P score c = minScore, goal needs the same
  convert hc using 2

lemma lowestScoring_subset {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) :
    lowestScoring P score ⊆ Finset.univ := by
  intro c hc
  exact Finset.mem_univ c

lemma scoreCandidate_le_of_mem_lowestScoring {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int) {c e : A}
    (hc : c ∈ lowestScoring P score) :
    scoreCandidate P score c ≤ scoreCandidate P score e := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · -- Unfold `lowestScoring` in the nonempty case.
    simp [lowestScoring, hA] at hc
    -- Work with the score-set and its minimum.
    set scoreSet : Finset Int := (Finset.univ.image (fun a : A => scoreCandidate P score a))
    have hScoreNonempty : scoreSet.Nonempty := by
      simpa [scoreSet, Finset.Nonempty] using hA.image (fun a : A => scoreCandidate P score a)
    set minScore : Int := scoreSet.min' hScoreNonempty
    have hcEq : scoreCandidate P score c = minScore := by
      simpa [scoreSet, minScore] using hc
    have heMem : scoreCandidate P score e ∈ scoreSet := by
      refine Finset.mem_image.mpr ?_
      exact ⟨e, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score e := by
      -- `min'` is below every member.
      simpa [minScore] using (Finset.min'_le (s := scoreSet) (x := scoreCandidate P score e) heMem)
    -- Rewrite `minScore` as `scoreCandidate ... c`.
    simpa [hcEq.symm] using hminle
  · -- Empty candidate set: `lowestScoring` is empty, so membership is impossible.
    simp [lowestScoring, hA] at hc

-- Cardinality decreases when removing a candidate
lemma card_restrict_lt {A : Type} [Fintype A] [DecidableEq A] (c : A) :
    Fintype.card {x : A // x ≠ c} < Fintype.card A :=
  Fintype.card_subtype_lt (x := c) (by simp)

lemma card_subtype_ne_eq {A : Type} [Fintype A] [DecidableEq A] (c : A) :
    Fintype.card {x : A // x ≠ c} = Fintype.card A - 1 := by
  classical
  -- Convert the subtype cardinality to a filtered finset cardinality.
  have h := (Fintype.card_subtype (α := A) (p := fun x => x ≠ c))
  -- Rewrite `{x | x ≠ c}` as `univ.erase c`.
  have hfilter : ({x : A | x ≠ c} : Finset A) = (Finset.univ.erase c) := by
    ext x
    by_cases hx : x = c <;> simp [hx]
  have h' : Fintype.card {x : A // x ≠ c} = (Finset.univ.erase c).card := by
    -- Avoid `simp` reducing the equality to `True`.
    have h' := h
    -- Rewrite the RHS finset using `hfilter`.
    rw [hfilter] at h'
    exact h'
  have herase : (Finset.univ.erase c).card = (Finset.univ : Finset A).card - 1 :=
    Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := c) (by simp)
  calc
    Fintype.card {x : A // x ≠ c} = (Finset.univ.erase c).card := h'
    _ = (Finset.univ : Finset A).card - 1 := herase
    _ = Fintype.card A - 1 := by simp [Finset.card_univ]

-- Lift a finset from a subtype back to the original type
noncomputable def liftFinset {A : Type} [DecidableEq A] {p : A → Prop}
    (s : Finset {x : A // p x}) : Finset A := by
  classical
  exact s.image (fun x => x.val)

lemma liftFinset_subset_of_prop {A : Type} [DecidableEq A] {p : A → Prop}
    (s : Finset {x : A // p x}) :
    ∀ x ∈ liftFinset s, p x := by
  intro x hx
  simp only [liftFinset, Finset.mem_image] at hx
  rcases hx with ⟨y, _, rfl⟩
  exact y.property

lemma not_mem_liftFinset_removed {A : Type} [DecidableEq A] {c : A}
    (s : Finset {x : A // x ≠ c}) : c ∉ liftFinset s := by
  classical
  intro hc
  -- Unfold `liftFinset` directly at the hypothesis.
  dsimp [liftFinset] at hc
  rcases Finset.mem_image.mp hc with ⟨x, _hx, hxval⟩
  exact x.property (by simpa using hxval)

/-!
## Main elimination procedure

We define the elimination procedure using well-founded recursion on the cardinality
of the candidate set.
-/

-- The core elimination procedure, parameterized by candidate type
noncomputable def scoringEliminationAux
    {V : Type} [Fintype V]
    (score : Nat → Nat → Int)
    : ∀ (A : Type) [Fintype A] [DecidableEq A], Profile V A → Finset A :=
  fun A inst_fin inst_dec P => by
    classical
    letI := inst_fin
    letI := inst_dec
    by_cases hcard : Fintype.card A ≤ 1
    · -- Base case: 0 or 1 candidate
      exact Finset.univ
    · -- Recursive case: eliminate lowest-scoring candidates
      push_neg at hcard
      let m := Fintype.card A
      let scoreVec := fun r => score m r
      let L := lowestScoring P scoreVec
      have hL : L.Nonempty := by
        apply lowestScoring_nonempty
        have hne : Nonempty A := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card A)
        exact @Finset.univ_nonempty A _ hne
      -- For each lowest-scoring candidate, recursively compute winners
      have hterm : ∀ c : A, Fintype.card {x : A // x ≠ c} < Fintype.card A :=
        fun c => card_restrict_lt c
      exact L.biUnion (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P c)))
termination_by A inst_fin _ _ => @Fintype.card A inst_fin
decreasing_by
  exact hterm c

-- The scoring elimination rule as a VotingRule
noncomputable def scoringEliminationRule (score : Nat → Nat → Int) : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    exact scoringEliminationAux score A P

end SocialChoice
