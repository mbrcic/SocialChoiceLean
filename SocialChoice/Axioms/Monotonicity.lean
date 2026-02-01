import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Meta

namespace SocialChoice

open Finset

def simpleLift {V A : Type} [Fintype V] [Fintype A]
    (P' P : Profile V A) (x : A) : Prop :=
  (∀ v a b, a ≠ x → b ≠ x → (Prefers P v a b ↔ Prefers P' v a b)) ∧
    ∀ a v, (Prefers P v x a → Prefers P' v x a) ∧
      (Prefers P' v a x → Prefers P v a x)

@[scAxiom]
def Monotonicity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P P' : Profile V A) (x : A),
    x ∈ f P → simpleLift P' P x → x ∈ f P'

lemma margin_eq_of_simpleLift {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x a b : A) (ha : a ≠ x) (hb : b ≠ x) :
    simpleLift P' P x → margin P a b = margin P' a b := by
  classical
  intro lift
  rcases lift with ⟨lift1, _⟩
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers P' v a b) ?_
    intro v
    exact lift1 v a b ha hb
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers P' v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers P' v b a) ?_
    intro v
    exact lift1 v b a hb ha
  dsimp [margin]
  simp [h1, h2]

lemma margin_le_of_simpleLift_ax {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x a : A} (hLift : simpleLift P' P x) :
    margin P' a x ≤ margin P a x := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [self_margin_zero]
  · have hcond :
        ∀ v : V, (Prefers P' v a x → Prefers P v a x) ∧
          (Prefers P v x a → Prefers P' v x a) := by
      intro v
      exact ⟨(hLift.2 a v).2, (hLift.2 a v).1⟩
    exact margin_lemma P' P a x hax hcond

lemma margin_le_of_simpleLift_xa {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x a : A} (hLift : simpleLift P' P x) :
    margin P x a ≤ margin P' x a := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [self_margin_zero]
  · have hcond :
        ∀ v : V, (Prefers P v x a → Prefers P' v x a) ∧
          (Prefers P' v a x → Prefers P v a x) := by
      intro v
      exact hLift.2 a v
    exact margin_lemma P P' x a (by simpa [eq_comm] using hax) hcond

lemma margin_le_of_simpleLift_other {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x y a : A} (hLift : simpleLift P' P x) (hy : y ≠ x) :
    margin P a y ≤ margin P' a y := by
  classical
  by_cases hax : a = x
  · have hxy : x ≠ y := by simpa [eq_comm] using hy
    have hcond :
        ∀ v : V, (Prefers P v x y → Prefers P' v x y) ∧
          (Prefers P' v y x → Prefers P v y x) := by
      intro v
      exact ⟨(hLift.2 y v).1, (hLift.2 y v).2⟩
    have h := margin_lemma P P' x y hxy hcond
    simpa [hax] using h
  · have hEq : margin P a y = margin P' a y :=
      margin_eq_of_simpleLift P P' x a y hax hy hLift
    exact le_of_eq hEq

end SocialChoice
