import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Axioms.Reversal

namespace SocialChoice

open Finset

noncomputable def margin {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Int := by
  classical
  exact
    Int.ofNat ((Finset.univ.filter (fun v => Prefers P v a b)).card) -
      Int.ofNat ((Finset.univ.filter (fun v => Prefers P v b a)).card)

def margin_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Prop :=
  0 < margin P a b

def skew_symmetric {A : Type} (M : A -> A -> Int) : Prop :=
  forall a b, M a b = -(M b a)

theorem margin_antisymmetric {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : skew_symmetric (margin P) := by
  classical
  intro a b
  dsimp [margin, skew_symmetric]
  ring

theorem self_margin_zero {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a : A) : margin P a a = 0 := by
  classical
  dsimp [margin]
  simp

theorem ne_of_margin_pos {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {a b : A} (h : margin_pos P a b) : a ≠ b := by
  intro hEq
  subst hEq
  have h0 : (0 : Int) < 0 := by
    simp [margin_pos, self_margin_zero] at h
  exact (lt_irrefl 0 h0)

lemma unanimous_margin {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) (x y : A) :
    (∀ v : V, Prefers P v x y) → margin_pos P x y := by
  classical
  intro hxy
  have hxy_card :
      (Finset.univ.filter (fun v => Prefers P v x y)).card = Fintype.card V := by
    have hxy_set :
        (Finset.univ.filter (fun v => Prefers P v x y)) = (Finset.univ : Finset V) := by
      ext v
      simp [hxy v]
    simp [hxy_set]
  have hyx_card : (Finset.univ.filter (fun v => Prefers P v y x)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hxyv : Prefers P v x y := hxy v
    have hcontra : ¬ Prefers P v y x := by
      let _ := P.pref v
      exact lt_asymm hxyv
    exact hcontra (by simpa using (Finset.mem_filter.mp hv).2)
  have hpos : (0 : Int) < (Fintype.card V : Int) := by
    exact Int.natCast_pos.mpr Fintype.card_pos
  dsimp [margin_pos, margin]
  simpa [hxy_card, hyx_card] using hpos

lemma unanimous_margin_eq_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    (∀ v : V, Prefers P v x y) → margin P x y = (Fintype.card V : Int) := by
  classical
  intro hxy
  have hxy_card :
      (Finset.univ.filter (fun v => Prefers P v x y)).card = Fintype.card V := by
    have hxy_set :
        (Finset.univ.filter (fun v => Prefers P v x y)) = (Finset.univ : Finset V) := by
      ext v
      simp [hxy v]
    simp [hxy_set]
  have hyx_card : (Finset.univ.filter (fun v => Prefers P v y x)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hxyv : Prefers P v x y := hxy v
    have hcontra : ¬ Prefers P v y x := by
      let _ := P.pref v
      exact lt_asymm hxyv
    exact hcontra (by simpa using (Finset.mem_filter.mp hv).2)
  dsimp [margin]
  simp [hxy_card, hyx_card]

lemma margin_reverse_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin (reverse_profile P) b a = margin P a b := by
  classical
  simp [margin, prefers_reverse_profile]

lemma margin_le_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin P a b ≤ (Fintype.card V : Int) := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card ≤ Fintype.card V := by
    simpa using (Finset.card_le_univ (s := Finset.univ.filter (fun v => Prefers P v a b)))
  have h1' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) ≤
        (Fintype.card V : Int) := by
    exact Int.ofNat_le_ofNat_of_le h1
  have h2' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card) ≥ 0 := by
    exact Int.natCast_nonneg _
  have hsub :
      Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card -
          Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    exact sub_le_self _ h2'
  have hmargin :
      margin P a b ≤ Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    simp [margin]
  exact hmargin.trans h1'

lemma unanimous_of_margin_ge_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    (Fintype.card V : Int) ≤ margin P a b → ∀ v : V, Prefers P v a b := by
  classical
  intro hle v
  by_contra hnot
  have hne : (Finset.univ.filter (fun v => Prefers P v a b)) ≠ (Finset.univ : Finset V) := by
    intro hEq
    have : v ∈ (Finset.univ.filter (fun v => Prefers P v a b)) := by
      simp [hEq]
    exact hnot (Finset.mem_filter.mp this).2
  have hcard_lt :
      (Finset.univ.filter (fun v => Prefers P v a b)).card < Fintype.card V := by
    exact (Finset.card_lt_iff_ne_univ _).2 hne
  have hcard_lt' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) <
        (Fintype.card V : Int) := by
    exact Int.ofNat_lt_ofNat_of_lt hcard_lt
  have hmargin_le :
      margin P a b ≤ Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    have h2' :
        (Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card) ≥ 0 := by
      exact Int.natCast_nonneg _
    have hsub :
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card -
            Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card ≤
          Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
      exact sub_le_self _ h2'
    simp [margin]
  have hlt : margin P a b < (Fintype.card V : Int) :=
    lt_of_le_of_lt hmargin_le hcard_lt'
  exact (not_lt_of_ge hle hlt)

lemma margin_pos_irrefl {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : ∀ x, ¬ margin_pos P x x := by
  intro x
  simp [margin_pos, self_margin_zero]

lemma margin_pos_asymm {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : ∀ x y, margin_pos P x y → ¬ margin_pos P y x := by
  intro x y hxy hyx
  have hskew : margin P y x = - margin P x y := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) y x
  have hpos : 0 < margin P x y := by
    simpa [margin_pos] using hxy
  have hneg : margin P y x < 0 := by
    simpa [hskew] using (neg_neg_of_pos hpos)
  have hyx' : 0 < margin P y x := by
    simpa [margin_pos] using hyx
  exact (lt_asymm hyx' hneg)

lemma margin_addVoter_eq_of_prefers {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) (h : ballot.lt a b) :
    margin (addVoter P ballot) a b = margin P a b + 1 := by
  classical
  have hcard_ab :
      (Finset.univ.filter (fun v : V ⊕ Unit => Prefers (addVoter P ballot) v a b)).card =
        (Finset.univ.filter (fun v : V => Prefers P v a b)).card + 1 := by
    let S0 : Finset V := Finset.univ.filter (fun v => Prefers P v a b)
    let S : Finset (V ⊕ Unit) :=
      Finset.univ.filter (fun v => Prefers (addVoter P ballot) v a b)
    have hS : S = insert (Sum.inr ()) (S0.image (Sum.inl : V → V ⊕ Unit)) := by
      ext v
      cases v with
      | inl v =>
          simp [S, S0, addVoter, Prefers, Finset.mem_image]
      | inr u =>
          cases u
          simp [S, S0, addVoter, Prefers, Finset.mem_image, h]
    have hnotmem : Sum.inr () ∉ S0.image (Sum.inl : V → V ⊕ Unit) := by
      simp [Finset.mem_image]
    have hinj : Function.Injective (Sum.inl : V → V ⊕ Unit) := by
      intro a b hEq
      cases hEq
      rfl
    have hcard : S.card = (S0.image (Sum.inl : V → V ⊕ Unit)).card + 1 := by
      have hcard' :
          (insert (Sum.inr ()) (S0.image (Sum.inl : V → V ⊕ Unit))).card =
            (S0.image (Sum.inl : V → V ⊕ Unit)).card + 1 :=
        Finset.card_insert_of_notMem hnotmem
      simp [hS]
    calc
      S.card = (S0.image (Sum.inl : V → V ⊕ Unit)).card + 1 := hcard
      _ = S0.card + 1 := by
        simpa using (Finset.card_image_of_injective S0 hinj)
  let _ := ballot
  have hba : ¬ ballot.lt b a := by
    intro hba
    exact lt_asymm (by simpa using h) (by simpa using hba)
  have hcard_ba :
      (Finset.univ.filter (fun v : V ⊕ Unit => Prefers (addVoter P ballot) v b a)).card =
        (Finset.univ.filter (fun v : V => Prefers P v b a)).card := by
    let S0 : Finset V := Finset.univ.filter (fun v => Prefers P v b a)
    let S : Finset (V ⊕ Unit) :=
      Finset.univ.filter (fun v => Prefers (addVoter P ballot) v b a)
    have hS : S = S0.image Sum.inl := by
      ext v
      cases v with
      | inl v =>
          simp [S, S0, addVoter, Prefers, Finset.mem_image]
      | inr u =>
          cases u
          simp [S, S0, addVoter, Prefers, Finset.mem_image, hba]
    have hinj : Function.Injective (Sum.inl : V → V ⊕ Unit) := by
      intro a b hEq
      cases hEq
      rfl
    calc
      S.card = (S0.image Sum.inl).card := by
        simp [hS]
        rfl
      _ = S0.card := by
        simpa using (Finset.card_image_of_injective S0 hinj)
  dsimp [margin]
  simp [hcard_ab, hcard_ba]
  ring

lemma margin_addVoter_eq_of_prefers_rev {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) (h : ballot.lt b a) :
    margin (addVoter P ballot) a b = margin P a b - 1 := by
  have hswap : margin (addVoter P ballot) b a = margin P b a + 1 :=
    margin_addVoter_eq_of_prefers P ballot b a h
  have hskewP : margin P a b = - margin P b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a b
  have hskewP' : margin (addVoter P ballot) a b = - margin (addVoter P ballot) b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := addVoter P ballot)) a b
  calc
    margin (addVoter P ballot) a b = - margin (addVoter P ballot) b a := hskewP'
    _ = - (margin P b a + 1) := by simp [hswap]
    _ = (- margin P b a) - 1 := by ring
    _ = margin P a b - 1 := by simp [hskewP]

lemma margin_le_addVoter {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) :
    margin P a b ≤ margin (addVoter P ballot) a b + 1 := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let _ := ballot
    have htr : a < b ∨ b < a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have hlt' : ballot.lt a b := by simpa using hlt
        have hmargin : margin (addVoter P ballot) a b = margin P a b + 1 :=
          margin_addVoter_eq_of_prefers P ballot a b hlt'
        linarith [hmargin]
    | inr hgt =>
        have hgt' : ballot.lt b a := by simpa using hgt
        have hmargin : margin (addVoter P ballot) a b = margin P a b - 1 :=
          margin_addVoter_eq_of_prefers_rev P ballot a b hgt'
        linarith [hmargin]

lemma margin_addVoter_le {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) :
    margin (addVoter P ballot) a b ≤ margin P a b + 1 := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let _ := ballot
    have htr : a < b ∨ b < a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have hlt' : ballot.lt a b := by simpa using hlt
        have hmargin : margin (addVoter P ballot) a b = margin P a b + 1 :=
          margin_addVoter_eq_of_prefers P ballot a b hlt'
        linarith [hmargin]
    | inr hgt =>
        have hgt' : ballot.lt b a := by simpa using hgt
        have hmargin : margin (addVoter P ballot) a b = margin P a b - 1 :=
          margin_addVoter_eq_of_prefers_rev P ballot a b hgt'
        linarith [hmargin]

lemma margin_lemma {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (a b : A) (_ : a ≠ b) :
    (∀ v : V, (Prefers P v a b → Prefers P' v a b) ∧
      (Prefers P' v b a → Prefers P v b a)) →
    margin P a b ≤ margin P' a b := by
  classical
  intro lift
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card ≤
        (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    refine cardinality_lemma (p := fun v => Prefers P v a b)
      (q := fun v => Prefers P' v a b) ?_
    intro v hv
    exact (lift v).1 hv
  have h2 :
      (Finset.univ.filter (fun v => Prefers P' v b a)).card ≤
        (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    refine cardinality_lemma (p := fun v => Prefers P' v b a)
      (q := fun v => Prefers P v b a) ?_
    intro v hv
    exact (lift v).2 hv
  have h1' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    exact Int.ofNat_le_ofNat_of_le h1
  have h2' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P' v b a)).card) ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    exact Int.ofNat_le_ofNat_of_le h2
  have hsub := sub_le_sub h1' h2'
  simpa [margin] using hsub

lemma margin_eq_margin_restrictProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    {P : Profile V A} {c : A} {a b : {x : A // x ≠ c}} :
    margin P a b = margin (restrictProfile P c) a b := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers (restrictProfile P c) v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers (restrictProfile P c) v a b) ?_
    intro v
    simp
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers (restrictProfile P c) v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers (restrictProfile P c) v b a) ?_
    intro v
    simp
  dsimp [margin]
  simp [h1, h2]

end SocialChoice
