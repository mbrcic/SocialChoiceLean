import SocialChoice.Profile

namespace SocialChoice

noncomputable local instance {A : Type*} [Fintype A] (c : A) : Fintype {x : A // x ≠ c} := by
  classical
  infer_instance

noncomputable def minusCandidate {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Profile V {x : A // x ≠ c} := by
  classical
  exact restrictCandidates P (fun x => x ≠ c)

def clones {V A : Type*} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}) : Prop :=
  D.Nonempty ∧
    ∀ (c' : {x : A // x ≠ c}), c' ∈ D →
      ∀ (x : {x : A // x ≠ c}) (v : V), x ∉ D →
        (Prefers P v c x ↔ Prefers P v c' x) ∧
          (Prefers P v x c ↔ Prefers P v x c')

def nonCloneChoiceIndClones (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}),
    clones P c D →
      ∀ a : {x : A // x ≠ c},
        a ∉ D → (a.1 ∈ f P ↔ a ∈ f (minusCandidate P c))

def cloneChoiceIndClones (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}),
    clones P c D →
      ((c ∉ f P ∧ ∀ c' : {x : A // x ≠ c}, c' ∈ D → (c' : A) ∉ f P) ↔
        ∀ c' : {x : A // x ≠ c}, c' ∈ D → c' ∉ f (minusCandidate P c))

end SocialChoice
