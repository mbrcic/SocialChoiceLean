import Pivato.Profiles

/-!
# Abstract rules on count-profile domains

This file encodes the paper's abstract correspondence model over domains
`D ⊆ N^{<V>}`.
-/

namespace Pivato

section Rules

variable {V X : Type*}

/-- A set-valued voting correspondence on a domain `D`. -/
abbrev RuleOn (D : Domain V) (X : Type*) :=
  {d : NProfile V // d ∈ D} → Set X

/-- General abstention axiom: the zero profile selects all alternatives. -/
def GeneralAbstention (D : Domain V) (F : RuleOn D X) : Prop :=
  ∀ (h0 : (0 : NProfile V) ∈ D), F ⟨0, h0⟩ = Set.univ

/-- Nonemptiness of outcomes for every profile in-domain. -/
def NonemptyOnDomain (D : Domain V) (F : RuleOn D X) : Prop :=
  ∀ d : {d : NProfile V // d ∈ D}, (F d).Nonempty

/-- Weak additivity from Pivato: closure under sums when winners overlap. -/
def WeaklyAdditive (D : Domain V) (F : RuleOn D X) : Prop :=
  ∀ ⦃d e : NProfile V⦄ (hd : d ∈ D) (he : e ∈ D),
    (F ⟨d, hd⟩ ∩ F ⟨e, he⟩).Nonempty → d + e ∈ D

/-- Reinforcement over a (possibly non-additively-closed) weakly additive domain. -/
def Reinforcement (D : Domain V) (F : RuleOn D X) : Prop :=
  WeaklyAdditive D F ∧
    ∀ ⦃d e : NProfile V⦄ (hd : d ∈ D) (he : e ∈ D) (hsum : d + e ∈ D),
      (F ⟨d, hd⟩ ∩ F ⟨e, he⟩).Nonempty →
        F ⟨d + e, hsum⟩ = F ⟨d, hd⟩ ∩ F ⟨e, he⟩

lemma reinforcement_weaklyAdditive {D : Domain V} {F : RuleOn D X} :
    Reinforcement D F → WeaklyAdditive D F :=
  And.left

lemma reinforcement_eq_inter {D : Domain V} {F : RuleOn D X}
    (hR : Reinforcement D F)
    {d e : NProfile V} (hd : d ∈ D) (he : e ∈ D) (hsum : d + e ∈ D)
    (hinter : (F ⟨d, hd⟩ ∩ F ⟨e, he⟩).Nonempty) :
    F ⟨d + e, hsum⟩ = F ⟨d, hd⟩ ∩ F ⟨e, he⟩ :=
  hR.2 hd he hsum hinter

lemma reinforcement_subset_add {D : Domain V} {F : RuleOn D X}
    (hR : Reinforcement D F)
    {d e : NProfile V} (hd : d ∈ D) (he : e ∈ D)
    (hinter : (F ⟨d, hd⟩ ∩ F ⟨e, he⟩).Nonempty) :
    F ⟨d, hd⟩ ∩ F ⟨e, he⟩ ⊆ F ⟨d + e, (hR.1 hd he hinter)⟩ := by
  intro x hx
  have hEq := hR.2 hd he (hR.1 hd he hinter) hinter
  simpa [hEq] using hx

lemma generalAbstention_nonempty {D : Domain V} {F : RuleOn D X} [Nonempty X]
    (hA : GeneralAbstention D F) (h0 : (0 : NProfile V) ∈ D) :
    (F ⟨0, h0⟩).Nonempty := by
  simp [hA h0]

end Rules

end Pivato
