import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

lemma dominatesSet_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (S : Finset A) :
    dominatesSet (P := P₁) S ↔ dominatesSet (P := P₂) S := by
  classical
  simp [dominatesSet, margin_pos, hmargin]

lemma topCycleSet_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A] [Nonempty A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    topCycleSet (P := P₁) = topCycleSet (P := P₂) := by
  classical
  have hdom₁ : dominatesSet (P := P₁) (topCycleSet (P := P₁)) :=
    topCycleSet_dominates (P := P₁)
  have hdom₁' : dominatesSet (P := P₂) (topCycleSet (P := P₁)) :=
    (dominatesSet_eq_of_margins (P₁ := P₁) (P₂ := P₂)
      (S := topCycleSet (P := P₁)) hmargin).1 hdom₁
  have hdom₂ : dominatesSet (P := P₂) (topCycleSet (P := P₂)) :=
    topCycleSet_dominates (P := P₂)
  have hmargin' : ∀ x y : A, margin P₂ x y = margin P₁ x y := by
    intro x y
    symm
    exact hmargin x y
  have hdom₂' : dominatesSet (P := P₁) (topCycleSet (P := P₂)) :=
    (dominatesSet_eq_of_margins (P₁ := P₂) (P₂ := P₁)
      (S := topCycleSet (P := P₂)) hmargin').1 hdom₂
  have hsubset₂₁ :
      topCycleSet (P := P₂) ⊆ topCycleSet (P := P₁) :=
    topCycleSet_subset_of_dominates (P := P₂) (S := topCycleSet (P := P₁)) hdom₁'
  have hsubset₁₂ :
      topCycleSet (P := P₁) ⊆ topCycleSet (P := P₂) :=
    topCycleSet_subset_of_dominates (P := P₁) (S := topCycleSet (P := P₂)) hdom₂'
  apply Finset.ext
  intro a
  constructor
  · intro ha
    exact hsubset₁₂ ha
  · intro ha
    exact hsubset₂₁ ha

theorem topCycle_marginBased : MarginBased topCycle := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  by_cases hA : Nonempty A
  ·
    let _ : Nonempty A := hA
    have hset :
        topCycleSet (P := P₁) = topCycleSet (P := P₂) :=
      topCycleSet_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
    simp [topCycle, hA, hset]
  ·
    simp [topCycle, hA]

end SocialChoice
