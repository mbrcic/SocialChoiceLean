import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Basic

namespace SocialChoice

open Finset

structure SetExtension (A : Type) where
  weak : Finset A → Finset A → Prop

def SetExtension.strict {A : Type} (E : SetExtension A) (s t : Finset A) : Prop :=
  E.weak s t ∧ ¬ E.weak t s

def SetExtension.incomp {A : Type} (E : SetExtension A) (s t : Finset A) : Prop :=
  ¬ E.weak s t ∧ ¬ E.weak t s

def SetExtension.Complete {A : Type} (E : SetExtension A) : Prop :=
  ∀ s t : Finset A, s.Nonempty → t.Nonempty → E.weak s t ∨ E.weak t s

def TopInSet {A : Type} [DecidableEq A] (r : LinearOrder A) (s : Finset A) (a : A) : Prop :=
  a ∈ s ∧ ∀ b : A, b ∈ s → b ≠ a → r.lt a b

def BottomInSet {A : Type} [DecidableEq A] (r : LinearOrder A) (s : Finset A) (a : A) : Prop :=
  a ∈ s ∧ ∀ b : A, b ∈ s → b ≠ a → r.lt b a

lemma exists_topInSet {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s : Finset A} (hs : s.Nonempty) : ∃ a, TopInSet r s a := by
  classical
  let _ := r
  refine ⟨s.min' hs, ?_⟩
  constructor
  · exact s.min'_mem hs
  · intro b hb hne
    have hle : s.min' hs ≤ b := s.min'_le b hb
    have hne' : s.min' hs ≠ b := by
      exact hne.symm
    have hlt : s.min' hs < b := lt_of_le_of_ne hle hne'
    simpa using hlt

lemma exists_bottomInSet {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s : Finset A} (hs : s.Nonempty) : ∃ a, BottomInSet r s a := by
  classical
  let _ := r
  refine ⟨s.max' hs, ?_⟩
  constructor
  · exact s.max'_mem hs
  · intro b hb hne
    have hle : b ≤ s.max' hs := s.le_max' b hb
    have hlt : b < s.max' hs := lt_of_le_of_ne hle hne
    simpa using hlt

def OptimistWeak {A : Type} [DecidableEq A] (r : LinearOrder A)
    (s t : Finset A) : Prop :=
  ∃ a b : A, TopInSet r s a ∧ TopInSet r t b ∧ r.le a b

def PessimistWeak {A : Type} [DecidableEq A] (r : LinearOrder A)
    (s t : Finset A) : Prop :=
  ∃ a b : A, BottomInSet r s a ∧ BottomInSet r t b ∧ r.le a b

def OptimistExtension {A : Type} [DecidableEq A] (r : LinearOrder A) : SetExtension A :=
  { weak := OptimistWeak r }

def PessimistExtension {A : Type} [DecidableEq A] (r : LinearOrder A) : SetExtension A :=
  { weak := PessimistWeak r }

def KellyWeak {A : Type} (r : LinearOrder A) (s t : Finset A) : Prop :=
  ∀ x ∈ s, ∀ y ∈ t, r.le x y

def KellyExtension {A : Type} (r : LinearOrder A) : SetExtension A :=
  { weak := KellyWeak r }

def FishburnWeak {A : Type} [DecidableEq A] (r : LinearOrder A) (s t : Finset A) : Prop :=
  (∀ x ∈ s \ t, ∀ y ∈ s ∩ t, r.le x y) ∧
    (∀ y ∈ s ∩ t, ∀ z ∈ t \ s, r.le y z) ∧
    (∀ x ∈ s \ t, ∀ z ∈ t \ s, r.le x z)

def FishburnExtension {A : Type} [DecidableEq A] (r : LinearOrder A) : SetExtension A :=
  { weak := FishburnWeak r }

lemma optimist_complete {A : Type} [DecidableEq A] (r : LinearOrder A) :
    SetExtension.Complete (OptimistExtension r) := by
  intro s t hs ht
  obtain ⟨a, ha⟩ := exists_topInSet r hs
  obtain ⟨b, hb⟩ := exists_topInSet r ht
  have hcomp : r.le a b ∨ r.le b a := by
    let _ := r
    simpa using (le_total a b)
  cases hcomp with
  | inl hle => exact Or.inl ⟨a, b, ha, hb, hle⟩
  | inr hle => exact Or.inr ⟨b, a, hb, ha, hle⟩

lemma pessimist_complete {A : Type} [DecidableEq A] (r : LinearOrder A) :
    SetExtension.Complete (PessimistExtension r) := by
  intro s t hs ht
  obtain ⟨a, ha⟩ := exists_bottomInSet r hs
  obtain ⟨b, hb⟩ := exists_bottomInSet r ht
  have hcomp : r.le a b ∨ r.le b a := by
    let _ := r
    simpa using (le_total a b)
  cases hcomp with
  | inl hle => exact Or.inl ⟨a, b, ha, hb, hle⟩
  | inr hle => exact Or.inr ⟨b, a, hb, ha, hle⟩

lemma optimist_no_incomp {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty) :
    ¬ (OptimistExtension r).incomp s t := by
  intro h
  have hcomp := optimist_complete r s t hs ht
  cases hcomp with
  | inl hw => exact h.1 hw
  | inr hw => exact h.2 hw

lemma pessimist_no_incomp {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty) :
    ¬ (PessimistExtension r).incomp s t := by
  intro h
  have hcomp := pessimist_complete r s t hs ht
  cases hcomp with
  | inl hw => exact h.1 hw
  | inr hw => exact h.2 hw

end SocialChoice
