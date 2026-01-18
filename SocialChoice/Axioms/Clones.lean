import Mathlib.Data.Set.Basic
import SocialChoice.Profile

/-!
TODO: this file contains two different definitions of independence of clones:
- `independence_of_clones`
- `nonCloneChoiceIndClones` and `cloneChoiceIndClones`

The former is taken from Delemazure and Peters and involves deleting all but one clone.
The latter is taken from Holliday and Pacuit and involves deleting one clone.

These need to be unified or proven to be equivalent.

TODO: Prove that independence of clones implies neutrality.
-/


namespace SocialChoice

noncomputable local instance {A : Type} [Fintype A] (c : A) : Fintype {x : A // x ≠ c} := by
  classical
  infer_instance

noncomputable instance instDecidablePredClone {A : Type} (X : Set A) (x : A) :
    DecidablePred (fun a : A => a ∉ X ∨ a = x) := by
  classical
  infer_instance

def clonePred {A : Type} (X : Set A) (x : A) : A → Prop := fun a => a ∉ X ∨ a = x

noncomputable instance instDecidablePredClonePred {A : Type} (X : Set A) (x : A) :
    DecidablePred (clonePred X x) := by
  classical
  simpa [clonePred] using (instDecidablePredClone (A := A) X x)

noncomputable instance instFintypeClonePred {A : Type} [Fintype A] (X : Set A) (x : A) :
    Fintype {a : A // clonePred X x a} := by
  classical
  infer_instance

noncomputable instance instDecidableEqCloneSubtype {A : Type} (X : Set A) (x : A) :
    DecidableEq {a : A // clonePred X x a} := by
  classical
  exact Classical.decEq _

/-! ## Clone sets and restriction helpers -/

/-- A clone set `X` (subset of candidates). -/
def CloneSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) : Prop :=
  X.Nonempty ∧
    ∀ v c, c ∉ X →
      (∀ x ∈ X, Prefers P v x c) ∨ (∀ x ∈ X, Prefers P v c x)

/-- Remove all clones in `X` except for the representative `x`. -/
noncomputable def removeClonesExcept {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) :
    Profile V {a : A // clonePred X x a} :=
  restrictCandidates P (clonePred X x)

lemma clonePred_swap {A : Type} [DecidableEq A] (X : Set A) (x x' a : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    clonePred X x a ↔ clonePred X x' ((Equiv.swap x x') a) := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [clonePred, Equiv.swap_apply_left]
  · by_cases hax' : a = x'
    · subst hax'
      simp [clonePred, Equiv.swap_apply_right, hxx', hx, hx', hax]
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

lemma cloneSwapEquiv_symm_apply_nonclone {A : Type} [DecidableEq A]
    {X : Set A} {x x' c : A} (hc : c ∉ X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (cloneSwapEquiv X x x' hx hx' hxx').symm ⟨c, Or.inl hc⟩ = ⟨c, Or.inl hc⟩ := by
  classical
  have hcx : c ≠ x := by
    intro h
    apply hc
    simpa [h] using hx
  have hcx' : c ≠ x' := by
    intro h
    apply hc
    simpa [h] using hx'
  apply Subtype.ext
  simp [cloneSwapEquiv, Equiv.swap_apply_def, hcx, hcx']

lemma cloneSwapEquiv_apply_rep {A : Type} [DecidableEq A]
    {X : Set A} {x x' : A} (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨x, Or.inr rfl⟩ = ⟨x', Or.inr rfl⟩ := by
  classical
  ext
  simp [cloneSwapEquiv, Equiv.swap_apply_left]

lemma cloneSwapEquiv_symm_apply_rep {A : Type} [DecidableEq A]
    {X : Set A} {x x' : A} (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (cloneSwapEquiv X x x' hx hx' hxx').symm ⟨x', Or.inr rfl⟩ = ⟨x, Or.inr rfl⟩ := by
  classical
  apply Subtype.ext
  simp [cloneSwapEquiv, Equiv.swap_apply_right]

/-- Clone set on a restricted candidate type. -/
def restrictCloneSet {A : Type} (X : Set A) (ℓ : A) : Set {a : A // a ≠ ℓ} :=
  {a | (a : A) ∈ X}

@[simp] lemma mem_restrictCloneSet {A : Type} {X : Set A} {ℓ : A} {a : {a : A // a ≠ ℓ}} :
    a ∈ restrictCloneSet X ℓ ↔ (a : A) ∈ X := by
  rfl

lemma restrictCloneSet_nonempty {A : Type} {X : Set A} {ℓ : A}
    (h : ∃ x ∈ X, x ≠ ℓ) : (restrictCloneSet X ℓ).Nonempty := by
  rcases h with ⟨x, hx, hxne⟩
  refine ⟨⟨x, hxne⟩, ?_⟩
  simpa [restrictCloneSet] using hx

@[simp] lemma prefers_removeClonesExcept_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) (v : V)
    (a b : {a : A // clonePred X x a}) :
    Prefers (removeClonesExcept P X x) v a b ↔ Prefers P v a b := by
  rfl

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

@[simp] lemma clonePred_restrictCloneSet_eq
  {A : Type} (X : Set A) (x ℓ : A) (hxℓ : x ≠ ℓ) :
  clonePred (restrictCloneSet (A := A) X ℓ) (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) =
    (fun a : {a : A // a ≠ ℓ} => clonePred X x a.1) := by
  funext a
  apply propext
  constructor
  · intro h
    rcases h with h | h
    · left
      intro haX
      apply h
      simpa [restrictCloneSet] using haX
    · right
      exact congrArg Subtype.val h
  · intro h
    rcases h with h | h
    · left
      intro haX
      apply h
      simpa [restrictCloneSet] using haX
    · right
      ext
      simpa using h

def IndependenceOfClones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
      (P : Profile V A) (X : Set A) (x : A),
    CloneSet P X → x ∈ X →
      (∀ c (hc : c ∉ X),
        (c ∈ f P ↔
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ f (removeClonesExcept P X x))) ∧
      ((∃ y, y ∈ X ∧ y ∈ f P) ↔
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ f (removeClonesExcept P X x))

noncomputable def minusCandidate {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Profile V {x : A // x ≠ c} := by
  classical
  exact restrictCandidates P (fun x => x ≠ c)

def clones {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}) : Prop :=
  D.Nonempty ∧
    ∀ (c' : {x : A // x ≠ c}), c' ∈ D →
      ∀ (x : {x : A // x ≠ c}) (v : V), x ∉ D →
        (Prefers P v c x ↔ Prefers P v c' x) ∧
          (Prefers P v x c ↔ Prefers P v x c')

lemma clones_of_cloneSet
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hXne : ∃ y ∈ X, y ≠ x) :
    clones P x (restrictCloneSet X x) := by
  classical
  rcases hX with ⟨_, hclone⟩
  refine ⟨restrictCloneSet_nonempty (X := X) (ℓ := x) hXne, ?_⟩
  intro c' hc' y v hy
  have hc'X : (c' : A) ∈ X := by
    simpa [restrictCloneSet] using hc'
  have hyX : (y : A) ∉ X := by
    intro hyX
    apply hy
    simpa [restrictCloneSet] using hyX
  let _ := P.pref v
  have hcase := hclone v (y : A) hyX
  cases hcase with
  | inl hall =>
      have hxpref : Prefers P v x y := hall x hx
      have hc'pref : Prefers P v c' y := hall c' hc'X
      have hxfalse : ¬ Prefers P v y x := by
        intro h
        exact lt_asymm hxpref h
      have hc'false : ¬ Prefers P v y c' := by
        intro h
        exact lt_asymm hc'pref h
      refine ⟨?_, ?_⟩
      · exact ⟨(fun _ => hc'pref), (fun _ => hxpref)⟩
      · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hc'false h).elim)⟩
  | inr hall =>
      have hxpref : Prefers P v y x := hall x hx
      have hc'pref : Prefers P v y c' := hall c' hc'X
      have hxfalse : ¬ Prefers P v x y := by
        intro h
        exact lt_asymm h hxpref
      have hc'false : ¬ Prefers P v c' y := by
        intro h
        exact lt_asymm h hc'pref
      refine ⟨?_, ?_⟩
      · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hc'false h).elim)⟩
      · exact ⟨(fun _ => hc'pref), (fun _ => hxpref)⟩

def NonCloneChoiceIndependenceOfClones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}),
    clones P c D →
      ∀ a : {x : A // x ≠ c},
        a ∉ D → (a.1 ∈ f P ↔ a ∈ f (minusCandidate P c))

def CloneChoiceIndependenceOfClones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}),
    clones P c D →
      ((c ∉ f P ∧ ∀ c' : {x : A // x ≠ c}, c' ∈ D → (c' : A) ∉ f P) ↔
        ∀ c' : {x : A // x ≠ c}, c' ∈ D → c' ∉ f (minusCandidate P c))

end SocialChoice
