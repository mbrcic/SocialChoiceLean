import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Basic

/-!
# Core abstract types for Pivato-style count-profile voting

This file introduces the foundational aliases and predicates used by the
continuation of the Pivato formalization.
-/

namespace Pivato

/-- Anonymous profile of nonnegative signal-counts with finite support. -/
abbrev NProfile (V : Type*) := V →₀ ℕ

/-- Integer-valued finite-support profile vectors. -/
abbrev ZProfile (V : Type*) := V →₀ ℤ

/-- A profile domain is a subset of anonymous finite-support count profiles. -/
abbrev Domain (V : Type*) := Set (NProfile V)

/-- Domain axiom from the paper: `0 ∈ D`. -/
def IsDomain {V : Type*} (D : Domain V) : Prop :=
  (0 : NProfile V) ∈ D

/-- Additive closure on domains of count profiles. -/
def DomainAddClosed {V : Type*} (D : Domain V) : Prop :=
  ∀ ⦃d e : NProfile V⦄, d ∈ D → e ∈ D → d + e ∈ D

/-- Purity/divisibility closure for domains:
if a positive multiple lies in the domain, then so does the base profile. -/
def DomainDivisible {V : Type*} (D : Domain V) : Prop :=
  ∀ ⦃d : NProfile V⦄ ⦃n : ℕ⦄, n ≠ 0 → n • d ∈ D → d ∈ D

/-- Paper-facing synonym for `DomainDivisible`. -/
abbrev DomainPure {V : Type*} (D : Domain V) : Prop := DomainDivisible D

/-- Cone condition used in Theorem 2: additive closure plus divisibility closure. -/
def IsCone {V : Type*} (D : Domain V) : Prop :=
  DomainAddClosed D ∧ DomainDivisible D

lemma isCone_addClosed {V : Type*} {D : Domain V} (h : IsCone D) : DomainAddClosed D :=
  h.1

lemma isCone_divisible {V : Type*} {D : Domain V} (h : IsCone D) :
    DomainDivisible D :=
  h.2

lemma isCone_pure {V : Type*} {D : Domain V} (h : IsCone D) :
    DomainPure D := h.2

end Pivato
