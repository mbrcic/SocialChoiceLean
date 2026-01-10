import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.CondorcetLoser

namespace SocialChoice

open Finset

/-!
# IRV Satisfies Independence of Clones

This file follows the proof sketch in
`SocialChoice/Rules/ScoringElimination/InstantRunoffVoting/CLONES-PROOF-SKETCH.md`.
-/

variable {V A : Type} [Fintype V] [Fintype A]

noncomputable local instance instDecidablePredClone {A : Type} (X : Set A) (x : A) :
    DecidablePred (fun a : A => a ∉ X ∨ a = x) := by
  classical
  infer_instance

noncomputable local instance instFintypeCloneSubtype {A : Type} [Fintype A] (X : Set A) (x : A) :
    Fintype {a : A // a ∉ X ∨ a = x} := by
  classical
  infer_instance

def clonePred (X : Set A) (x : A) : A → Prop := fun a => a ∉ X ∨ a = x

noncomputable local instance instDecidablePredClonePred {A : Type} (X : Set A) (x : A) :
    DecidablePred (clonePred X x) := by
  classical
  simpa [clonePred] using (instDecidablePredClone (A := A) X x)

noncomputable local instance instFintypeClonePred {A : Type} [Fintype A] (X : Set A) (x : A) :
    Fintype {a : A // clonePred X x a} := by
  classical
  simpa [clonePred] using (instFintypeCloneSubtype (A := A) X x)

noncomputable local instance instDecidableEqCloneSubtype {A : Type} [DecidableEq A] (X : Set A) (x : A) :
    DecidableEq {a : A // a ∉ X ∨ a = x} := by
  classical
  infer_instance

/-! ## Clone sets and restriction helpers -/

/-- A clone set `X` (subset of candidates). -/
def CloneSet (P : Profile V A) (X : Set A) : Prop :=
  X.Nonempty ∧
    ∀ v c, c ∉ X →
      (∀ x ∈ X, Prefers P v x c) ∨ (∀ x ∈ X, Prefers P v c x)

/-- Remove all clones in `X` except for the representative `x`. -/
noncomputable def removeClonesExcept (P : Profile V A) (X : Set A) (x : A) :
    Profile V {a : A // a ∉ X ∨ a = x} :=
  restrictCandidates P (fun a => a ∉ X ∨ a = x)

lemma clonePred_swap {A : Type} [DecidableEq A] (X : Set A) (x x' a : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    clonePred X x a ↔ clonePred X x' ((Equiv.swap x x') a) := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [clonePred, Equiv.swap_apply_left]
  · by_cases hax' : a = x'
    · subst hax'
      simp [clonePred, Equiv.swap_apply_right, hxx', hx, hx']
    · have hswap : (Equiv.swap x x') a = a := by
        simp [Equiv.swap_apply_def, hax, hax']
      simp [clonePred, hswap, hax, hax']

noncomputable def cloneSwapEquiv {A : Type} [DecidableEq A]
    (X : Set A) (x x' : A) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    {a : A // clonePred X x a} ≃ {a : A // clonePred X x' a} :=
  (Equiv.swap x x').subtypeEquiv (clonePred_swap (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx'))

lemma cloneSwapEquiv_apply_nonclone {A : Type} [DecidableEq A]
    {X : Set A} {x x' c : A} (hc : c ∉ X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨c, Or.inl hc⟩ = ⟨c, Or.inl hc⟩ := by
  classical
  have hcx : c ≠ x := by
    intro h
    apply hc
    simpa [h] using hx
  have hcx' : c ≠ x' := by
    intro h
    apply hc
    simpa [h] using hx'
  have hswap : (Equiv.swap x x') c = c := by
    simp [Equiv.swap_apply_def, hcx, hcx']
  ext
  simp [cloneSwapEquiv, hswap]

lemma cloneSwapEquiv_apply_rep {A : Type} [DecidableEq A]
    {X : Set A} {x x' : A} (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨x, Or.inr rfl⟩ = ⟨x', Or.inr rfl⟩ := by
  classical
  ext
  simp [cloneSwapEquiv, Equiv.swap_apply_left]

/-- Clone set on a restricted candidate type. -/
def restrictCloneSet (X : Set A) (ℓ : A) : Set {a : A // a ≠ ℓ} :=
  {a | (a : A) ∈ X}

@[simp] lemma mem_restrictCloneSet {X : Set A} {ℓ : A} {a : {a : A // a ≠ ℓ}} :
    a ∈ restrictCloneSet X ℓ ↔ (a : A) ∈ X := by
  rfl

@[simp] lemma prefers_removeClonesExcept_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) (v : V)
    (a b : {a : A // a ∉ X ∨ a = x}) :
    Prefers (removeClonesExcept P X x) v a b ↔ Prefers P v a b := by
  rfl

lemma removeClonesExcept_swap_eq
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    removeClonesExcept P X x' =
      relabelProfile (removeClonesExcept P X x)
        (cloneSwapEquiv X x x' hx hx' hxx') := by
  ext v
  rfl


lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {a : A} (ha : p a) :
    a ∈ liftWinners s ↔ (⟨a, ha⟩ : {a : A // p a}) ∈ s := by
  classical
  -- `liftWinners` is `image Subtype.val`.
  simp [liftWinners, Finset.mem_image, ha]

lemma restrictCloneSet_nonempty {X : Set A} {ℓ : A}
    (h : ∃ x ∈ X, x ≠ ℓ) : (restrictCloneSet X ℓ).Nonempty := by
  rcases h with ⟨x, hx, hxne⟩
  refine ⟨⟨x, hxne⟩, ?_⟩
  simpa [restrictCloneSet] using hx

lemma cloneSet_restrictProfile
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (ℓ : A) (hX : CloneSet P X)
    (hXne : ∃ x ∈ X, x ≠ ℓ) :
    CloneSet (restrictProfile P ℓ) (restrictCloneSet X ℓ) := by
  classical
  rcases hX with ⟨_hXnonempty, hclone⟩
  refine ⟨restrictCloneSet_nonempty (X := X) (ℓ := ℓ) hXne, ?_⟩
  intro v c hc
  have hc' : (c : A) ∉ X := by
    intro hmem
    apply hc
    simpa [restrictCloneSet] using hmem
  have hcase := hclone v (c : A) hc'
  cases hcase with
  | inl hall =>
    left
    intro x hx
    have hx' : (x : A) ∈ X := by
      simpa [restrictCloneSet] using hx
    simpa using (hall x hx')

lemma scoringEliminationAux_swap_rep
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    scoringEliminationAux pluralityScore _ (removeClonesExcept P X x') =
      (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
        (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding := by
  classical
  have h :=
    scoringEliminationAux_equiv (score := pluralityScore)
      (P := removeClonesExcept P X x) (e := cloneSwapEquiv X x x' hx hx' hxx')
  simpa [removeClonesExcept_swap_eq (P := P) (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx')] using h

lemma nonclone_winner_swap
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' c : A)
    (hc : c ∉ X) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x') := by
  classical
  have hswap := scoringEliminationAux_swap_rep (P := P) (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx')
  -- Use the map characterization.
  have hmem :
      (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding ↔
      (cloneSwapEquiv X x x' hx hx' hxx').symm
          (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
    mem_relabelWinners (e := cloneSwapEquiv X x x' hx hx' hxx') _ _
  -- The swap equivalence fixes non-clones.
  have hfix :
      (cloneSwapEquiv X x x' hx hx' hxx').symm
          (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) =
        (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x}) := by
    simpa [cloneSwapEquiv_apply_nonclone (X := X) (x := x) (x' := x') (c := c)
      (hc := hc) (hx := hx) (hx' := hx') (hxx' := hxx')] using rfl
  constructor
  · intro hcwin
    have hcwin' : (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding := by
      exact Finset.mem_map.mpr ⟨⟨c, Or.inl hc⟩, hcwin, rfl⟩
    have hcwin'' := (hmem.mp hcwin')
    simpa [hfix] using hcwin''
      |> (by
        simpa [hswap] using (hmem.mp hcwin'))
  · intro hcwin
    have hcwin' :
        (cloneSwapEquiv X x x' hx hx' hxx').symm
          (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) := by
      simpa [hfix] using hcwin
    have hcwin'' :
        (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
          (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
            (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding :=
      (hmem.mpr hcwin')
    simpa [hswap] using hcwin''

lemma clone_winner_swap
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x') := by
  classical
  have hswap := scoringEliminationAux_swap_rep (P := P) (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx')
  have hmem :
      (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding ↔
      (cloneSwapEquiv X x x' hx hx' hxx').symm
          (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
    mem_relabelWinners (e := cloneSwapEquiv X x x' hx hx' hxx') _ _
  have hsymm :
      (cloneSwapEquiv X x x' hx hx' hxx').symm
          (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) =
        (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) := by
    have := cloneSwapEquiv_apply_rep (X := X) (x := x) (x' := x')
      (hx := hx) (hx' := hx') (hxx' := hxx')
    simpa using congrArg (Equiv.symm (cloneSwapEquiv X x x' hx hx' hxx')) this
  constructor
  · intro hxwin
    have hxwin' :
        (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
          (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
            (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding :=
      Finset.mem_map.mpr ⟨⟨x, Or.inr rfl⟩, hxwin, by
        simpa using
          (cloneSwapEquiv_apply_rep (X := X) (x := x) (x' := x') (hx := hx) (hx' := hx')
            (hxx' := hxx'))⟩
    have hxwin'' := (hmem.mp hxwin')
    simpa [hsymm] using hxwin''
      |> (by
        simpa [hswap] using (hmem.mp hxwin'))
  · intro hxwin
    have hxwin' :
        (cloneSwapEquiv X x x' hx hx' hxx').symm
          (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) := by
      simpa [hsymm] using hxwin
    have hxwin'' :
        (⟨x', Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x'}) ∈
          (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
            (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding :=
      (hmem.mpr hxwin')
    simpa [hswap] using hxwin''
  | inr hall =>
    right
    intro x hx
    have hx' : (x : A) ∈ X := by
      simpa [restrictCloneSet] using hx
    simpa using (hall x hx')


/-! ## Plurality score facts under clone restriction -/

noncomputable def pluralityScoreVec : Nat → Int :=
  fun r => if r = 0 then 1 else 0

lemma cloneSet_prefers_equiv
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x x' y : A} (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∉ X) (v : V) :
    (Prefers P v x y ↔ Prefers P v x' y) ∧
      (Prefers P v y x ↔ Prefers P v y x') := by
  classical
  rcases hX with ⟨_, hclone⟩
  let _ := P.pref v
  have hcase := hclone v y hy
  cases hcase with
  | inl hall =>
    have hxpref : Prefers P v x y := hall x hx
    have hx'pref : Prefers P v x' y := hall x' hx'
    have hxfalse : ¬ Prefers P v y x := by
      intro h
      exact lt_asymm (hall x hx) h
    have hx'false : ¬ Prefers P v y x' := by
      intro h
      exact lt_asymm (hall x' hx') h
    refine ⟨?_, ?_⟩
    · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩
    · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
  | inr hall =>
    have hxpref : Prefers P v y x := hall x hx
    have hx'pref : Prefers P v y x' := hall x' hx'
    have hxfalse : ¬ Prefers P v x y := by
      intro h
      exact lt_asymm h (hall x hx)
    have hx'false : ¬ Prefers P v x' y := by
      intro h
      exact lt_asymm h (hall x' hx')
    refine ⟨?_, ?_⟩
    · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
    · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩

lemma topRank_removeClonesExcept_iff_of_nonclone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) (v : V) :
    TopRank P v a ↔
      TopRank (removeClonesExcept P X x) v (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x}) := by
  classical
  constructor
  · intro htop d hd
    have := htop d (by
      intro hEq
      apply hd
      ext
      simpa using hEq)
    simpa using this
  · intro htop d hd
    by_cases hdx : d ∈ X
    · -- If `d` is a clone, use clone symmetry and the fact that `x` is in the restricted profile.
      have hxa : Prefers P v a x := by
        have htop' := htop (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) (by
          intro hEq
          apply ha
          have hxEq : x = a := congrArg Subtype.val hEq
          simpa [hxEq] using hx)
        simpa using htop'
      have hrel :=
        (cloneSet_prefers_equiv P X hX hdx hx ha v).2
      -- `Prefers P v a d ↔ Prefers P v a x`
      exact (hrel.mpr hxa)
    · -- `d` is a non-clone, so it appears in the restricted profile.
      have htop' := htop (⟨d, Or.inl hdx⟩ : {a : A // a ∉ X ∨ a = x}) (by
        intro hEq
        apply hd
        simpa using congrArg Subtype.val hEq)
      simpa using htop'

lemma topRank_clone_implies_rep
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) (v : V) :
    TopRank P v y →
      TopRank (removeClonesExcept P X x) v (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) := by
  classical
  intro htop d hd
  by_cases hdx : (d : A) ∈ X
  · -- Only `x` from `X` remains; the other case is `d = x`.
    have hxEq : (d : A) = x := by
      cases d.property with
      | inl hnot =>
        exact (hnot hdx).elim
      | inr hEq =>
        exact hEq
    exact (hd (by
      ext
      simpa using hxEq)).elim
  · -- For non-clones, use clone symmetry with `y`.
    have hrel := (cloneSet_prefers_equiv P X hX hy hx hdx v).1
    have hy_top : Prefers P v y d := htop d (by
      intro hEq
      apply hdx
      simpa [hEq] using hy)
    exact (hrel.mp hy_top)

lemma votersTop_card_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) :
    (votersTop P a).card =
      (votersTop (removeClonesExcept P X x) (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x})).card := by
  classical
  refine cardinality_lemma2 (p := fun v => TopRank P v a)
    (q := fun v =>
      TopRank (removeClonesExcept P X x) v (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x})) ?_
  intro v
  exact topRank_removeClonesExcept_iff_of_nonclone P X x hX hx ha v

lemma votersTop_card_rep_ge_clone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) :
    (votersTop P y).card ≤
      (votersTop (removeClonesExcept P X x) (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x})).card := by
  classical
  refine cardinality_lemma (p := fun v => TopRank P v y)
    (q := fun v =>
      TopRank (removeClonesExcept P X x) v (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x})) ?_
  intro v hv
  exact topRank_clone_implies_rep P X x y hX hx hy v hv

lemma score_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) :
    scoreCandidate P pluralityScoreVec a =
      scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
        (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x}) := by
  classical
  have hcard :=
    votersTop_card_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := ha)
  calc
    scoreCandidate P pluralityScoreVec a
        = ((votersTop P a).card : Int) := by
            simpa [pluralityScoreVec] using (pluralityScore_eq_votersTop_card (P := P) (c := a))
    _ = ((votersTop (removeClonesExcept P X x)
            (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x})).card : Int) := by
            exact_mod_cast hcard
    _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x}) := by
            symm
            simpa [pluralityScoreVec] using
              (pluralityScore_eq_votersTop_card (P := removeClonesExcept P X x)
                (c := (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x})))

lemma score_rep_ge_clone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) :
    scoreCandidate P pluralityScoreVec y ≤
      scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
        (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) := by
  classical
  have hcard :=
    votersTop_card_rep_ge_clone (P := P) (X := X) (x := x) (y := y) (hX := hX) (hx := hx) (hy := hy)
  have hcard' : (votersTop P y).card ≤
      (votersTop (removeClonesExcept P X x)
        (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x})).card := hcard
  have hcardInt :
      ((votersTop P y).card : Int) ≤
        ((votersTop (removeClonesExcept P X x)
          (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x})).card : Int) := by
    exact_mod_cast hcard'
  calc
    scoreCandidate P pluralityScoreVec y
        = ((votersTop P y).card : Int) := by
            simpa [pluralityScoreVec] using (pluralityScore_eq_votersTop_card (P := P) (c := y))
    _ ≤ ((votersTop (removeClonesExcept P X x)
          (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x})).card : Int) := hcardInt
    _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
          (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) := by
          symm
          simpa [pluralityScoreVec] using
            (pluralityScore_eq_votersTop_card (P := removeClonesExcept P X x)
              (c := (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x})))

/-! ## Lowest-scoring characterization -/

lemma lowestScoring_iff_forall_le {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int)
    (hA : (Finset.univ : Finset A).Nonempty) (c : A) :
    c ∈ lowestScoring P score ↔
      ∀ d : A, scoreCandidate P score c ≤ scoreCandidate P score d := by
  classical
  let scoreSet : Finset Int := Finset.univ.image (fun a => scoreCandidate P score a)
  have hScoreNonempty : scoreSet.Nonempty := by
    simpa [scoreSet, Finset.Nonempty] using hA.image (fun a => scoreCandidate P score a)
  let minScore : Int := scoreSet.min' hScoreNonempty
  constructor
  · intro hc d
    have hc' : scoreCandidate P score c = minScore := by
      simpa [lowestScoring, hA, scoreSet, minScore] using hc
    have hmem : scoreCandidate P score d ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score d :=
      Finset.min'_le scoreSet _ hmem
    simpa [hc'] using hminle
  · intro hle
    have hmem : scoreCandidate P score c ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score c :=
      Finset.min'_le scoreSet _ hmem
    have hmin_mem : minScore ∈ scoreSet := Finset.min'_mem scoreSet hScoreNonempty
    rcases Finset.mem_image.mp hmin_mem with ⟨d, _hd, hdeq⟩
    have hle' : scoreCandidate P score c ≤ minScore := by
      simpa [hdeq] using hle d
    have hmin_eq : scoreCandidate P score c = minScore := le_antisymm hle' hminle
    have hc : c ∈ (Finset.univ.filter (fun a => scoreCandidate P score a = minScore)) := by
      exact Finset.mem_filter.mpr ⟨by simp, hmin_eq⟩
    simpa [lowestScoring, hA, scoreSet, minScore] using hc

lemma lowestScoring_nonclone_preserved
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {ℓ : A} (hℓ : ℓ ∉ X)
    (hℓ_low : ℓ ∈ lowestScoring P pluralityScoreVec) :
    (⟨ℓ, Or.inl hℓ⟩ : {a : A // a ∉ X ∨ a = x}) ∈
      lowestScoring (removeClonesExcept P X x) pluralityScoreVec := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := by
    rcases hX.1 with ⟨y, _⟩
    have : Nonempty A := ⟨y⟩
    exact Finset.univ_nonempty
  have hAhat : (Finset.univ : Finset {a : A // a ∉ X ∨ a = x}).Nonempty := by
    letI : Nonempty {a : A // a ∉ X ∨ a = x} := ⟨⟨x, Or.inr rfl⟩⟩
    exact Finset.univ_nonempty
  have hℓ_low' :
      ∀ d : A, scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec d :=
    (lowestScoring_iff_forall_le (P := P) (score := pluralityScoreVec) hA ℓ).1 hℓ_low
  have hle :
      ∀ d : {a : A // a ∉ X ∨ a = x},
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨ℓ, Or.inl hℓ⟩ : {a : A // a ∉ X ∨ a = x})
          ≤ scoreCandidate (removeClonesExcept P X x) pluralityScoreVec d := by
    intro d
    cases d.property with
    | inl hdnot =>
      have hℓ_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      have hd_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hdnot)
      calc
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // a ∉ X ∨ a = x})
            = scoreCandidate P pluralityScoreVec ℓ := by
                symm
                exact hℓ_eq
        _ ≤ scoreCandidate P pluralityScoreVec d := hℓ_low' d
        _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨d, Or.inl hdnot⟩ : {a : A // a ∉ X ∨ a = x}) := by
                exact hd_eq
    | inr hdx =>
      have hℓ_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      have hx_le :=
        score_rep_ge_clone (P := P) (X := X) (x := x) (y := x) (hX := hX) (hx := hx) (hy := hx)
      have hℓx : scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec x :=
        hℓ_low' x
      have hxEq : (d : A) = x := hdx
      have hdEq : d = (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) := by
        ext
        simp [hxEq]
      calc
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // a ∉ X ∨ a = x})
            = scoreCandidate P pluralityScoreVec ℓ := by
                symm
                exact hℓ_eq
        _ ≤ scoreCandidate P pluralityScoreVec x := hℓx
        _ ≤ scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) := hx_le
        _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec d := by
              simp [hdEq]
  exact (lowestScoring_iff_forall_le (P := removeClonesExcept P X x)
      (score := pluralityScoreVec) hAhat
      (⟨ℓ, Or.inl hℓ⟩ : {a : A // a ∉ X ∨ a = x})).2 hle

/-! ## Main induction (proof sketch) -/

def irv_nonclone_prop
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  ∀ a (ha : a ∉ X),
    a ∈ scoringEliminationAux pluralityScore A P ↔
      (⟨a, Or.inl ha⟩ : {a : A // a ∉ X ∨ a = x}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)

def irv_clone_prop
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  (∃ y, y ∈ X ∧ y ∈ scoringEliminationAux pluralityScore A P) ↔
    (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) ∈
      scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)

def independence_of_clones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
      (P : Profile V A) (X : Set A) (x : A),
    CloneSet P X → x ∈ X →
      (∀ c (hc : c ∉ X),
        (c ∈ f P ↔
          (⟨c, Or.inl hc⟩ : {a : A // a ∉ X ∨ a = x}) ∈ f (removeClonesExcept P X x))) ∧
      ((∃ y, y ∈ X ∧ y ∈ f P) ↔
        (⟨x, Or.inr rfl⟩ : {a : A // a ∉ X ∨ a = x}) ∈ f (removeClonesExcept P X x))

end SocialChoice
