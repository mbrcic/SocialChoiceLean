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

end SocialChoice
