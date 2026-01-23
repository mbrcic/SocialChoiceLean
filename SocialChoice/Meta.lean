/-
Copyright (c) 2024 Social Choice in Lean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominik Peters
-/
import SocialChoice.Profile
import Lean.Elab.Command

/-!
# Meta-level Predicates for Social Choice Theory

This file defines predicates for reasoning about relationships between voting rules
and between axioms. These are useful for:
- Proving derived results (e.g., Schulze satisfies Condorcet via refinement)
- Documentation tooling that can parse theorem types to build tables

## Main Definitions

* `Refines f g`: Rule `f` refines `g` (always returns a subset of winners)
* `PreservedUnderRefinement Z`: Axiom `Z` transfers from coarser to finer rules
* `PreservedUnderCoarsening Z`: Axiom `Z` transfers from finer to coarser rules
* `Implies Z₁ Z₂`: Axiom `Z₁` implies axiom `Z₂` for all rules

## Custom Attributes

* `@[scAxiom]`: Tag a definition as a social choice axiom
* `@[scRule]`: Tag a definition as a voting rule

## Main Results

* `Refines.refl`, `Refines.trans`: Refinement is a preorder
* `Implies.refl`, `Implies.trans`: Implication is a preorder
* `preservedUnderCoarsening_iff_neg_preservedUnderRefinement`: Characterization via negation
-/

/-! ## Custom Attributes for Tagging Axioms and Rules -/

/-- Attribute to mark a definition as a social choice axiom.
Used by documentation tooling to enumerate all axioms. -/
initialize scAxiom : Lean.TagAttribute ←
  Lean.registerTagAttribute `scAxiom "Social choice axiom"

/-- Attribute to mark a definition as a voting rule.
Used by documentation tooling to enumerate all rules. -/
initialize scRule : Lean.TagAttribute ←
  Lean.registerTagAttribute `scRule "Voting rule"

namespace SocialChoice

/-! ## Refinement Between Rules -/

/-- A voting rule `f` refines `g` if `f` always returns a subset of `g`'s winners.
Equivalently, `f` is "finer" or "more selective" than `g`. -/
def Refines (f g : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A), f P ⊆ g P

namespace Refines

@[refl]
theorem refl (f : VotingRule) : Refines f f :=
  fun _ => Finset.Subset.refl _

theorem trans {f g h : VotingRule} (hfg : Refines f g) (hgh : Refines g h) : Refines f h :=
  fun P => Finset.Subset.trans (hfg P) (hgh P)

instance : Trans Refines Refines Refines where
  trans := trans

end Refines

/-! ## Preservation Under Refinement/Coarsening -/

/-- An axiom is preserved under refinement if: whenever a coarser rule satisfies
the axiom and a finer rule refines it, the finer rule also satisfies the axiom.
Assumes both rules are total (nonempty) voting rules. -/
def PreservedUnderRefinement (Z : VotingRule → Prop) : Prop :=
  ∀ f g, IsVotingRule f → IsVotingRule g → Refines f g → Z g → Z f

/-- An axiom is preserved under coarsening if: whenever a finer rule satisfies
the axiom and a coarser rule is refined by it, the coarser rule also satisfies the axiom.
Assumes both rules are total (nonempty) voting rules.

Example: "Semi-Condorcet" (Condorcet winner is among the winners, but ties allowed)
is preserved under coarsening. -/
def PreservedUnderCoarsening (Z : VotingRule → Prop) : Prop :=
  ∀ f g, IsVotingRule f → IsVotingRule g → Refines f g → Z f → Z g

/-- Preservation under coarsening is equivalent to preservation under refinement
for the negation of the axiom. -/
theorem preservedUnderCoarsening_iff_neg_preservedUnderRefinement
    (Z : VotingRule → Prop) :
    PreservedUnderCoarsening Z ↔ PreservedUnderRefinement (fun f => ¬Z f) := by
  constructor
  · intro hcoarse f g hf_total hg_total hfg hnZg hZf
    exact hnZg (hcoarse f g hf_total hg_total hfg hZf)
  · intro hrefine f g hf_total hg_total hfg hZf
    by_contra hnZg
    exact hrefine f g hf_total hg_total hfg hnZg hZf

/-! ## Implication Between Axioms -/

/-- An axiom `Z₁` implies axiom `Z₂` if every total rule satisfying `Z₁`
also satisfies `Z₂`. -/
def Implies (Z₁ Z₂ : VotingRule → Prop) : Prop :=
  ∀ f, IsVotingRule f → Z₁ f → Z₂ f

namespace Implies

@[refl]
theorem refl (Z : VotingRule → Prop) : Implies Z Z :=
  fun _ _ hZ => hZ

theorem trans {Z₁ Z₂ Z₃ : VotingRule → Prop}
    (h₁₂ : Implies Z₁ Z₂) (h₂₃ : Implies Z₂ Z₃) : Implies Z₁ Z₃ :=
  fun f hf hZ₁ => h₂₃ f hf (h₁₂ f hf hZ₁)

instance : Trans Implies Implies Implies where
  trans := trans

/-- Apply an implication to derive one axiom from another. -/
theorem apply {Z₁ Z₂ : VotingRule → Prop} (h : Implies Z₁ Z₂)
    {f : VotingRule} (hf_total : IsVotingRule f) (hZf : Z₁ f) : Z₂ f :=
  h f hf_total hZf

end Implies

/-! ## Useful Combinators -/

/-- Apply preservation under refinement to derive an axiom for a finer rule. -/
theorem PreservedUnderRefinement.apply {Z : VotingRule → Prop}
    (hZ : PreservedUnderRefinement Z) {f g : VotingRule}
    (hf_total : IsVotingRule f) (hg_total : IsVotingRule g)
    (hfg : Refines f g) (hZg : Z g) : Z f :=
  hZ f g hf_total hg_total hfg hZg

/-- Apply preservation under coarsening to derive an axiom for a coarser rule. -/
theorem PreservedUnderCoarsening.apply {Z : VotingRule → Prop}
    (hZ : PreservedUnderCoarsening Z) {f g : VotingRule}
    (hf_total : IsVotingRule f) (hg_total : IsVotingRule g)
    (hfg : Refines f g) (hZf : Z f) : Z g :=
  hZ f g hf_total hg_total hfg hZf

/-! ## Interaction Between Refinement and Implication -/

/-- If axiom Z₁ implies Z₂, and Z₁ is preserved under refinement, and Z₂ is preserved
under coarsening, this doesn't give us much. But if Z₁ is preserved under refinement,
then so is the conjunction Z₁ ∧ Z₂ for any Z₂ implied by Z₁. -/
theorem PreservedUnderRefinement.and_of_implies {Z₁ Z₂ : VotingRule → Prop}
    (hZ₁ : PreservedUnderRefinement Z₁) (hImpl : Implies Z₁ Z₂) :
    PreservedUnderRefinement (fun f => Z₁ f ∧ Z₂ f) :=
  fun f g hf_total hg_total hfg ⟨hZg₁, _⟩ =>
    let hZf₁ := hZ₁ f g hf_total hg_total hfg hZg₁
    ⟨hZf₁, hImpl f hf_total hZf₁⟩

end SocialChoice
