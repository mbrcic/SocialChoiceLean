import SocialChoice.Axioms.Clones
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Margin

namespace SocialChoice

open Finset

noncomputable section

noncomputable def collapseSet {A : Type} [Fintype A]
    (X : Set A) (x : A) (S : Finset A) :
    Finset {a : A // clonePred X x a} := by
  classical
  exact S.image (fun a =>
    if ha : a ∉ X then
      (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})
    else
      (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}))

noncomputable def liftSet {A : Type} [Fintype A]
    (X : Set A) (x : A) (T : Finset {a : A // clonePred X x a}) : Finset A := by
  classical
  exact T.image (fun a : {a : A // clonePred X x a} => (a : A)) ∪
    if (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ T then
      (Finset.univ.filter fun a => a ∈ X)
    else
      ∅

lemma mem_collapseSet_of_val_mem {A : Type} [Fintype A]
    (X : Set A) (x : A) (S : Finset A)
    (a : {a : A // clonePred X x a}) (haS : (a : A) ∈ S) :
    a ∈ collapseSet X x S := by
  classical
  unfold collapseSet
  refine Finset.mem_image.mpr ?_
  refine ⟨(a : A), haS, ?_⟩
  by_cases haX : (a : A) ∉ X
  · have haEq : (⟨(a : A), Or.inl haX⟩ : {a : A // clonePred X x a}) = a := by
      apply Subtype.ext
      rfl
    simp [haX, haEq]
  · have haInX : (a : A) ∈ X := not_not.mp haX
    have haEqx : (a : A) = x := by
      rcases a.2 with haNotX | haEqx
      · exact (haNotX haInX).elim
      · exact haEqx
    have haEqRep : a = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
      apply Subtype.ext
      simp [haEqx]
    simp [haEqRep]

lemma collapseSet_mem_nonclone_iff {A : Type} [Fintype A]
    (X : Set A) (x : A) (hx : x ∈ X) (S : Finset A)
    {c : A} (hc : c ∉ X) :
    (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ collapseSet X x S ↔ c ∈ S := by
  classical
  constructor
  · intro hmem
    unfold collapseSet at hmem
    rcases Finset.mem_image.mp hmem with ⟨a, haS, haEq⟩
    by_cases haX : a ∉ X
    · have hac : a = c := by
        have h' :
            (if haX : a ∉ X then
                (⟨a, Or.inl haX⟩ : {a : A // clonePred X x a})
              else
                (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})) =
              (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
          simpa using haEq
        simpa [haX] using congrArg Subtype.val h'
      simpa [hac] using haS
    · have hxc : x = c := by
        have h' :
            (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) =
              (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
          simpa [haX] using haEq
        exact congrArg Subtype.val h'
      have : c ∈ X := by simpa [hxc] using hx
      exact (hc this).elim
  · intro hcS
    unfold collapseSet
    refine Finset.mem_image.mpr ?_
    refine ⟨c, hcS, ?_⟩
    simp [hc]

lemma collapseSet_rep_mem_iff {A : Type} [Fintype A]
    (X : Set A) (x : A) (hx : x ∈ X) (S : Finset A) :
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ collapseSet X x S ↔
      ∃ y, y ∈ S ∧ y ∈ X := by
  classical
  constructor
  · intro hmem
    unfold collapseSet at hmem
    rcases Finset.mem_image.mp hmem with ⟨a, haS, haEq⟩
    by_cases haX : a ∉ X
    · have hax : a = x := by
        have h' :
            (if haX : a ∉ X then
                (⟨a, Or.inl haX⟩ : {a : A // clonePred X x a})
              else
                (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})) =
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          simpa using haEq
        simpa [haX] using congrArg Subtype.val h'
      have : x ∉ X := by simpa [hax] using haX
      exact (this hx).elim
    · exact ⟨a, haS, not_not.mp haX⟩
  · rintro ⟨y, hyS, hyX⟩
    unfold collapseSet
    refine Finset.mem_image.mpr ?_
    refine ⟨y, hyS, ?_⟩
    by_cases hyNot : y ∉ X
    · exact (hyNot hyX).elim
    · simp [hyNot]

lemma liftSet_mem_nonclone_iff {A : Type} [Fintype A]
    (X : Set A) (x : A) (T : Finset {a : A // clonePred X x a})
    {c : A} (hc : c ∉ X) :
    c ∈ liftSet X x T ↔ (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ T := by
  classical
  constructor
  · intro hmem
    unfold liftSet at hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · rcases Finset.mem_image.mp hmem with ⟨a, haT, haEq⟩
      have hac : (a : A) = c := by simpa using haEq
      have haEq' : a = (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
        apply Subtype.ext
        simp [hac]
      simpa [haEq'] using haT
    · by_cases hrep : (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ T
      · have hcX : c ∈ X := by
          simpa [hrep] using hmem
        exact (hc hcX).elim
      · simp [hrep] at hmem
  · intro hcT
    unfold liftSet
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨(⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}), hcT, rfl⟩

lemma exists_clone_mem_liftSet_iff {A : Type} [Fintype A]
    (X : Set A) (x : A) (hx : x ∈ X)
    (T : Finset {a : A // clonePred X x a}) :
    (∃ y, y ∈ X ∧ y ∈ liftSet X x T) ↔
      (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ T := by
  classical
  constructor
  · rintro ⟨y, hyX, hyLift⟩
    unfold liftSet at hyLift
    rcases Finset.mem_union.mp hyLift with hyLift | hyLift
    · rcases Finset.mem_image.mp hyLift with ⟨a, haT, haEq⟩
      have hay : (a : A) = y := by simpa using haEq
      have hyEqx : y = x := by
        have hpred : clonePred X x y := by simpa [hay] using a.2
        rcases hpred with hyNotX | hyEqx
        · exact (hyNotX hyX).elim
        · exact hyEqx
      have haEqRep : a = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
        apply Subtype.ext
        simp [hay, hyEqx]
      simpa [haEqRep] using haT
    · by_cases hrep : (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ T
      · exact hrep
      · simp [hrep] at hyLift
  · intro hrep
    refine ⟨x, hx, ?_⟩
    unfold liftSet
    simp [hrep, hx]

@[simp] lemma margin_removeClonesExcept_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (a b : {a : A // clonePred X x a}) :
    margin (removeClonesExcept P X x) a b = margin P a b := by
  classical
  simp [margin, removeClonesExcept]

@[simp] lemma margin_pos_removeClonesExcept_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (a b : {a : A // clonePred X x a}) :
    margin_pos (removeClonesExcept P X x) a b ↔ margin_pos P a b := by
  simp [margin_pos]

lemma margin_eq_clone_vs_nonclone {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x y b : A} (hx : x ∈ X) (hy : y ∈ X) (hb : b ∉ X) :
    margin P y b = margin P x b := by
  classical
  have h₁ :
      (Finset.univ.filter (fun v => Prefers P v y b)).card =
        (Finset.univ.filter (fun v => Prefers P v x b)).card := by
    refine cardinality_lemma2
      (p := fun v => Prefers P v y b) (q := fun v => Prefers P v x b) ?_
    intro v
    exact (cloneSet_prefers_equiv (P := P) (X := X) (hX := hX)
      (x := x) (x' := y) (y := b) hx hy hb v).1.symm
  have h₂ :
      (Finset.univ.filter (fun v => Prefers P v b y)).card =
        (Finset.univ.filter (fun v => Prefers P v b x)).card := by
    refine cardinality_lemma2
      (p := fun v => Prefers P v b y) (q := fun v => Prefers P v b x) ?_
    intro v
    exact (cloneSet_prefers_equiv (P := P) (X := X) (hX := hX)
      (x := x) (x' := y) (y := b) hx hy hb v).2.symm
  simp [margin, h₁, h₂]

lemma margin_pos_clone_vs_nonclone_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x y b : A} (hx : x ∈ X) (hy : y ∈ X) (hb : b ∉ X) :
    margin_pos P y b ↔ margin_pos P x b := by
  simp [margin_pos, margin_eq_clone_vs_nonclone (P := P) (X := X) (hX := hX)
    (hx := hx) (hy := hy) (hb := hb)]

lemma margin_eq_nonclone_vs_clone {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x y b : A} (hx : x ∈ X) (hy : y ∈ X) (hb : b ∉ X) :
    margin P b y = margin P b x := by
  have hxy : margin P y b = margin P x b :=
    margin_eq_clone_vs_nonclone (P := P) (X := X) (hX := hX) (hx := hx) (hy := hy) (hb := hb)
  calc
    margin P b y = - margin P y b := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P) b y)
    _ = - margin P x b := by simp [hxy]
    _ = margin P b x := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P) b x).symm

lemma margin_pos_nonclone_vs_clone_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x y b : A} (hx : x ∈ X) (hy : y ∈ X) (hb : b ∉ X) :
    margin_pos P b y ↔ margin_pos P b x := by
  simp [margin_pos, margin_eq_nonclone_vs_clone (P := P) (X := X) (hX := hX)
    (hx := hx) (hy := hy) (hb := hb)]

lemma dominatesSet_collapseSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) (S : Finset A)
    (hS : dominatesSet P S) :
    dominatesSet (removeClonesExcept P X x) (collapseSet X x S) := by
  classical
  rcases hS with ⟨hS_ne, hS_dom⟩
  refine ⟨?_, ?_⟩
  · rcases hS_ne with ⟨a, haS⟩
    refine ⟨
      if haX : a ∉ X then
        (⟨a, Or.inl haX⟩ : {a : A // clonePred X x a})
      else
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}),
      ?_⟩
    unfold collapseSet
    exact Finset.mem_image.mpr ⟨a, haS, rfl⟩
  · intro a ha b hb
    have hbS : (b : A) ∉ S := by
      intro hbS
      exact hb (mem_collapseSet_of_val_mem (X := X) (x := x) (S := S) b hbS)
    by_cases haNotX : (a : A) ∉ X
    · have haS : (a : A) ∈ S :=
        (collapseSet_mem_nonclone_iff (X := X) (x := x) (hx := hx) (S := S)
          (c := (a : A)) haNotX).1 ha
      have hpos : margin_pos P (a : A) (b : A) :=
        hS_dom (a : A) haS (b : A) hbS
      exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x) a b).2 hpos
    · have haXmem : (a : A) ∈ X := not_not.mp haNotX
      have hax : (a : A) = x := by
        rcases a.2 with haNotX' | hax
        · exact (haNotX' haXmem).elim
        · exact hax
      have haRep : a = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
        apply Subtype.ext
        simp [hax]
      have hrepMem : (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ collapseSet X x S := by
        simpa [haRep] using ha
      rcases (collapseSet_rep_mem_iff (X := X) (x := x) (hx := hx) (S := S)).1 hrepMem with
        ⟨y, hyS, hyX⟩
      have hbNotX : (b : A) ∉ X := by
        intro hbXmem
        have hbx : (b : A) = x := by
          rcases b.2 with hbNotX' | hbx
          · exact (hbNotX' hbXmem).elim
          · exact hbx
        have hbRep : b = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          apply Subtype.ext
          simp [hbx]
        exact hb (by simpa [hbRep] using hrepMem)
      have hyb : margin_pos P y (b : A) :=
        hS_dom y hyS (b : A) hbS
      have hxb : margin_pos P x (b : A) :=
        (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := y) (b := (b : A)) hx hyX hbNotX).1 hyb
      have hab : margin_pos P (a : A) (b : A) := by
        simpa [hax] using hxb
      exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x) a b).2 hab

lemma dominatesSet_liftSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X)
    (T : Finset {a : A // clonePred X x a})
    (hT : dominatesSet (removeClonesExcept P X x) T) :
    dominatesSet P (liftSet X x T) := by
  classical
  rcases hT with ⟨hT_ne, hT_dom⟩
  refine ⟨?_, ?_⟩
  · rcases hT_ne with ⟨a, haT⟩
    refine ⟨(a : A), ?_⟩
    unfold liftSet
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, haT, rfl⟩)
  · intro a ha b hb
    by_cases haNotX : a ∉ X
    · have haT :
        (⟨a, Or.inl haNotX⟩ : {a : A // clonePred X x a}) ∈ T :=
        (liftSet_mem_nonclone_iff (X := X) (x := x) (T := T) (c := a) haNotX).1 ha
      by_cases hbNotX : b ∉ X
      · have hbT :
            (⟨b, Or.inl hbNotX⟩ : {a : A // clonePred X x a}) ∉ T := by
          intro hbT
          exact hb ((liftSet_mem_nonclone_iff (X := X) (x := x) (T := T) (c := b) hbNotX).2 hbT)
        have hab' :
            margin_pos (removeClonesExcept P X x)
              (⟨a, Or.inl haNotX⟩ : {a : A // clonePred X x a})
              (⟨b, Or.inl hbNotX⟩ : {a : A // clonePred X x a}) :=
          hT_dom _ haT _ hbT
        exact (margin_pos_removeClonesExcept_iff
          (P := P) (X := X) (x := x)
          (⟨a, Or.inl haNotX⟩ : {a : A // clonePred X x a})
          (⟨b, Or.inl hbNotX⟩ : {a : A // clonePred X x a})).1 hab'
      · have hbX : b ∈ X := not_not.mp hbNotX
        have hrepNot :
            (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∉ T := by
          intro hrep
          have hbLift : b ∈ liftSet X x T := by
            unfold liftSet
            simp [hrep, hbX]
          exact hb hbLift
        have hax :
            margin_pos (removeClonesExcept P X x)
              (⟨a, Or.inl haNotX⟩ : {a : A // clonePred X x a})
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) :=
          hT_dom _ haT _ hrepNot
        have hax' : margin_pos P a x :=
          (margin_pos_removeClonesExcept_iff
            (P := P) (X := X) (x := x)
            (⟨a, Or.inl haNotX⟩ : {a : A // clonePred X x a})
            (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).1 hax
        have hab : margin_pos P a b :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := b) (b := a) hx hbX haNotX).2 hax'
        exact hab
    · have haX : a ∈ X := not_not.mp haNotX
      have hrep : (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ T :=
        (exists_clone_mem_liftSet_iff (X := X) (x := x) (hx := hx) (T := T)).1
          ⟨a, haX, ha⟩
      have hbNotX : b ∉ X := by
        intro hbX
        have hbLift : b ∈ liftSet X x T := by
          unfold liftSet
          simp [hrep, hbX]
        exact hb hbLift
      have hbT :
          (⟨b, Or.inl hbNotX⟩ : {a : A // clonePred X x a}) ∉ T := by
        intro hbT
        exact hb ((liftSet_mem_nonclone_iff (X := X) (x := x) (T := T) (c := b) hbNotX).2 hbT)
      have hxb' :
          margin_pos (removeClonesExcept P X x)
            (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})
            (⟨b, Or.inl hbNotX⟩ : {a : A // clonePred X x a}) :=
        hT_dom _ hrep _ hbT
      have hxb : margin_pos P x b :=
        (margin_pos_removeClonesExcept_iff
          (P := P) (X := X) (x := x)
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})
          (⟨b, Or.inl hbNotX⟩ : {a : A // clonePred X x a})).1 hxb'
      exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
        (x := x) (y := a) (b := b) hx haX hbNotX).2 hxb

set_option compiler.extract_closed false in
theorem topCycleSet_removeClonesExcept_independence
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A)
    [Nonempty A] [Nonempty {a : A // clonePred X x a}]
    (hX : CloneSet P X) (hx : x ∈ X) :
    (∀ c (hc : c ∉ X),
      c ∈ topCycleSet (P := P) ↔
        (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
          topCycleSet (P := removeClonesExcept P X x)) ∧
    ((∃ y, y ∈ X ∧ y ∈ topCycleSet (P := P)) ↔
      (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
        topCycleSet (P := removeClonesExcept P X x)) := by
  classical
  let S : Finset A := topCycleSet (P := P)
  let T : Finset {a : A // clonePred X x a} := topCycleSet (P := removeClonesExcept P X x)
  have hSdom : dominatesSet P S := by
    simpa [S] using topCycleSet_dominates (P := P)
  have hTdom : dominatesSet (removeClonesExcept P X x) T := by
    simpa [T] using topCycleSet_dominates (P := removeClonesExcept P X x)
  have hcollapse : dominatesSet (removeClonesExcept P X x) (collapseSet X x S) :=
    dominatesSet_collapseSet (P := P) (X := X) (x := x) hX hx S hSdom
  have hlift : dominatesSet P (liftSet X x T) :=
    dominatesSet_liftSet (P := P) (X := X) (x := x) hX hx T hTdom
  have hTsubset : T ⊆ collapseSet X x S :=
    topCycleSet_subset_of_dominates (P := removeClonesExcept P X x)
      (S := collapseSet X x S) hcollapse
  have hSsubset : S ⊆ liftSet X x T :=
    topCycleSet_subset_of_dominates (P := P) (S := liftSet X x T) hlift
  refine ⟨?_, ?_⟩
  · intro c hc
    constructor
    · intro hcS
      have hcLift : c ∈ liftSet X x T := by
        exact hSsubset (by simpa [S] using hcS)
      have hcT :
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ T :=
        (liftSet_mem_nonclone_iff (X := X) (x := x) (T := T) (c := c) hc).1 hcLift
      simpa [T]
        using hcT
    · intro hcT
      have hcColl :
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ collapseSet X x S :=
        hTsubset (by simpa [T] using hcT)
      have hcS :
          c ∈ S :=
        (collapseSet_mem_nonclone_iff (X := X) (x := x) (hx := hx) (S := S)
          (c := c) hc).1 hcColl
      simpa [S] using hcS
  · constructor
    · rintro ⟨y, hyX, hyS⟩
      have hyLift : y ∈ liftSet X x T := by
        exact hSsubset (by simpa [S] using hyS)
      exact (exists_clone_mem_liftSet_iff (X := X) (x := x) (hx := hx) (T := T)).1
        ⟨y, hyX, hyLift⟩
    · intro hrepT
      have hrepColl :
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ collapseSet X x S :=
        hTsubset (by simpa [T] using hrepT)
      have hExists :
          ∃ y, y ∈ S ∧ y ∈ X :=
        (collapseSet_rep_mem_iff (X := X) (x := x) (hx := hx) (S := S)).1 hrepColl
      rcases hExists with ⟨y, hyS, hyX⟩
      exact ⟨y, hyX, by simpa [S] using hyS⟩

set_option compiler.extract_closed false in
theorem topCycle_independenceOfClones : IndependenceOfClones topCycle := by
  intro V A _ _ _ P X x hX hx
  classical
  let rep : {a : A // clonePred X x a} := ⟨x, Or.inr rfl⟩
  have hA : Nonempty A := ⟨x⟩
  have hB : Nonempty {a : A // clonePred X x a} := ⟨rep⟩
  let _ : Nonempty A := hA
  let _ : Nonempty {a : A // clonePred X x a} := hB
  have hmain := topCycleSet_removeClonesExcept_independence
    (P := P) (X := X) (x := x) hX hx
  have htopA :
      topCycle P = topCycleSet (P := P) := by
    simp [topCycle, hA]
  have htopB :
      topCycle (removeClonesExcept P X x) =
        topCycleSet (P := removeClonesExcept P X x) := by
    simp [topCycle, hB]
  refine ⟨?_, ?_⟩
  · intro c hc
    constructor
    · intro hcTop
      have hcSet : c ∈ topCycleSet (P := P) := by simpa [htopA] using hcTop
      have hcSet' :
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
            topCycleSet (P := removeClonesExcept P X x) :=
        (hmain.1 c hc).1 hcSet
      simpa [htopB] using hcSet'
    · intro hcTop
      have hcSet :
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
            topCycleSet (P := removeClonesExcept P X x) := by
        simpa [htopB] using hcTop
      have hcSet' : c ∈ topCycleSet (P := P) :=
        (hmain.1 c hc).2 hcSet
      simpa [htopA] using hcSet'
  · constructor
    · rintro ⟨y, hyX, hyTop⟩
      have hySet : y ∈ topCycleSet (P := P) := by simpa [htopA] using hyTop
      have hrepSet :
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
            topCycleSet (P := removeClonesExcept P X x) :=
        hmain.2.1 ⟨y, hyX, hySet⟩
      simpa [htopB] using hrepSet
    · intro hrepTop
      have hrepSet :
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
            topCycleSet (P := removeClonesExcept P X x) := by
        simpa [htopB] using hrepTop
      rcases hmain.2.2 hrepSet with ⟨y, hyX, hySet⟩
      refine ⟨y, hyX, ?_⟩
      simpa [htopA] using hySet

end

end SocialChoice
