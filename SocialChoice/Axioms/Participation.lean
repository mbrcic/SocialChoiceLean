import SocialChoice.Profile
import SocialChoice.Axioms.Core

namespace SocialChoice

def PositiveInvolvement (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (ballot : LinearOrder A),
    c ∈ f P → BallotTop ballot c → c ∈ f (addVoter P ballot)

def NegativeInvolvement (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (ballot : LinearOrder A),
    c ∉ f P → BallotBottom ballot c → c ∉ f (addVoter P ballot)

abbrev Electorate (U : Type) (S : Finset U) := {u // u ∈ S}

instance (U : Type) [DecidableEq U] (S : Finset U) : Fintype (Electorate U S) := by
  classical
  simpa [Electorate] using (Fintype.subtype S (by intro x; rfl))

def liftVoter {U : Type} [DecidableEq U] {V : Finset U} (u : U) (v : Electorate U V) :
    Electorate U (insert u V) :=
  ⟨v.1, by simp [v.2]⟩

def newVoter {U : Type} [DecidableEq U] {V : Finset U} (u : U) (hu : u ∉ V) :
    Electorate U (insert u V) :=
  ⟨u, by simp [hu]⟩

noncomputable def restrictElectorate {U A : Type} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) (S : Finset U) (hS : S ⊆ W) :
    Profile (Electorate U S) A :=
  { pref := fun v => Q.pref ⟨v.1, hS v.2⟩ }

lemma restrictElectorate_agrees {U A : Type} [DecidableEq U] [Fintype A] {W S : Finset U}
    (Q : Profile (Electorate U W) A) (hS : S ⊆ W) (u : U)
    (hSu : insert u S ⊆ W) :
    ∀ v : Electorate U S,
      (restrictElectorate Q (insert u S) hSu).pref (liftVoter (u := u) v) =
        (restrictElectorate Q S hS).pref v := by
  intro v
  rfl

lemma restrictElectorate_self {U A : Type} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) :
    restrictElectorate Q W (by intro x hx; exact hx) = Q := by
  cases Q
  rfl

lemma restrictElectorate_eq_of_subset_proof {U A : Type} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) {S : Finset U} (h₁ h₂ : S ⊆ W) :
    restrictElectorate Q S h₁ = restrictElectorate Q S h₂ := by
  cases Q with
  | mk pref =>
      apply congrArg (fun f => Profile.mk f)
      funext v
      have hsub : (⟨v.1, h₁ v.2⟩ : Electorate U W) = ⟨v.1, h₂ v.2⟩ := by
        apply Subtype.ext
        rfl
      simp [hsub]

def UpperSet {A : Type} [DecidableEq A] (r : LinearOrder A) (S : Finset A) : Prop :=
  ∀ ⦃x y : A⦄, r.lt x y → y ∈ S → x ∈ S

lemma upperSet_mem_of_not_lt {A : Type} [DecidableEq A]
    {r : LinearOrder A} {S : Finset A} (hS : UpperSet r S)
    {x y : A} (hx : x ∈ S) (hnot : ¬ r.lt x y) : y ∈ S := by
  by_cases hxy : y = x
  · simpa [hxy] using hx
  · have hlt_or_gt : r.lt y x ∨ r.lt x y := lt_or_gt_of_ne hxy
    cases hlt_or_gt with
    | inl hlt => exact hS hlt hx
    | inr hgt => exact (False.elim (hnot hgt))

def ResoluteParticipation (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A) (x y : A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    f P = {x} →
    f Q = {y} →
    ¬ (Q.pref (newVoter (u := u) (V := V) hu)).lt x y

lemma resoluteParticipation_leaving {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) :
    ∀ {U A : Type} [DecidableEq U] [Fintype A]
        (V : Finset U) (u : U) (hu : u ∉ V)
        (P : Profile (Electorate U V) A)
        (Q : Profile (Electorate U (insert u V)) A) (x y : A),
      (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
      f Q = {x} →
      f P = {y} →
      ¬ (Q.pref (newVoter (u := u) (V := V) hu)).lt y x := by
  intro U A _ _ V u hu P Q x y hagree hx hy
  apply hpart (V := V) (u := u) hu P Q y x
  · exact hagree
  · exact hy
  · exact hx

lemma resoluteParticipation_superset {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) :
    ∀ {U A : Type} [DecidableEq U] [Fintype A] [DecidableEq A]
        (V W : Finset U) (hVW : V ⊆ W)
        (Q : Profile (Electorate U W) A) (S : Finset A) (x : A),
      f (restrictElectorate Q V hVW) = {x} →
      x ∈ S →
      (∀ w (hw : w ∈ W \ V),
        UpperSet (Q.pref ⟨w, (Finset.mem_sdiff.mp hw).1⟩) S) →
      f Q ⊆ S := by
  intro U A _ _ _ V W hVW Q S x hx hxS hUpper
  classical
  let T : Finset U := W \ V
  have hEqset0 : V ∪ (∅ : Finset U) = V := by simp
  have hVW' : V ∪ (∅ : Finset U) ⊆ W := by
    intro z hz
    exact hVW (by simpa using hz)
  have hx0 : f (restrictElectorate Q (V ∪ (∅ : Finset U)) hVW') = {x} := by
    convert hx
  have hTsub : T ⊆ W := by
    simp [T]
  have hVunion : ∀ s : Finset U, s ⊆ T → V ∪ s ⊆ W := by
    intro s hs
    exact Finset.union_subset hVW (Finset.Subset.trans hs hTsub)
  have hprop :
      ∀ s : Finset U, ∀ hs : s ⊆ T,
        ∀ y, f (restrictElectorate Q (V ∪ s) (hVunion s hs)) = {y} → y ∈ S := by
    intro s hs
    revert hs
    refine Finset.induction_on s ?base ?step
    · intro _ y hy
      have hx1 :
          f (restrictElectorate Q (V ∪ (∅ : Finset U)) (hVunion ∅ (by simp [T]))) = {x} := by
        have hEqprof :
            restrictElectorate Q (V ∪ (∅ : Finset U)) hVW' =
              restrictElectorate Q (V ∪ (∅ : Finset U)) (hVunion ∅ (by simp [T])) := by
          exact restrictElectorate_eq_of_subset_proof Q _ _
        simpa [hEqprof] using hx0
      have hxy : x = y := by
        have hxy' : ({x} : Finset A) = {y} := by simpa [hx1] using hy
        have hxmem : x ∈ ({y} : Finset A) := by
          simpa [hxy'] using (by simp : x ∈ ({x} : Finset A))
        simpa using hxmem
      simpa [hxy] using hxS
    · intro a s ha ih hs y hy
      have hsT : s ⊆ T := by
        intro z hz
        exact hs (by simp [hz])
      have haT : a ∈ T := by
        exact hs (by simp)
      let Ssmall : Finset U := V ∪ s
      have hSsmall : Ssmall ⊆ W := hVunion s hsT
      let Sbig : Finset U := insert a Ssmall
      have haW : a ∈ W := hTsub haT
      have hSbig : Sbig ⊆ W := Finset.insert_subset haW hSsmall
      have hcard_small : (f (restrictElectorate Q Ssmall hSsmall)).card = 1 := by
        simpa using (hf (restrictElectorate Q Ssmall hSsmall))
      rcases Finset.card_eq_one.mp hcard_small with ⟨x', hx'⟩
      have hx'_mem : x' ∈ S := by
        apply ih hsT x' hx'
      have hagree :
          ∀ v : Electorate U Ssmall,
            (restrictElectorate Q Sbig hSbig).pref (liftVoter (u := a) v) =
              (restrictElectorate Q Ssmall hSsmall).pref v := by
        intro v
        rfl
      have hy' : f (restrictElectorate Q Sbig hSbig) = {y} := by
        convert hy
        · simp [Sbig, Ssmall]
        · simp [Sbig, Ssmall]
      have hnot :
          ¬ ((restrictElectorate Q Sbig hSbig).pref
              (newVoter (u := a) (V := Ssmall) (by
                have haV : a ∉ V := (Finset.mem_sdiff.mp (by simpa [T] using haT)).2
                simp [Ssmall, haV, ha]))).lt x' y := by
        apply hpart (V := Ssmall) (u := a) ?_ (restrictElectorate Q Ssmall hSsmall)
            (restrictElectorate Q Sbig hSbig) x' y
        · exact hagree
        · exact hx'
        · exact hy'
        ·
          have haV : a ∉ V := (Finset.mem_sdiff.mp (by simpa [T] using haT)).2
          simp [Ssmall, haV, ha]
      have hUpper_a : UpperSet (Q.pref ⟨a, haW⟩) S := by
        exact hUpper a (by simpa [T] using haT)
      have hnot' :
          ¬ (Q.pref ⟨a, haW⟩).lt x' y := by
        simpa [restrictElectorate, newVoter, Ssmall] using hnot
      exact upperSet_mem_of_not_lt hUpper_a hx'_mem hnot'
  have hW : V ∪ T = W := by
    simpa [T] using (Finset.union_sdiff_of_subset hVW)
  have hWT : V ∪ T ⊆ W := by
    simp [hW]
  have hsubset : f (restrictElectorate Q (V ∪ T) hWT) ⊆ S := by
    intro y hy
    have hcard : (f (restrictElectorate Q (V ∪ T) hWT)).card = 1 := by
      simpa using (hf (restrictElectorate Q (V ∪ T) hWT))
    rcases Finset.card_eq_one.mp hcard with ⟨z, hz⟩
    have hy' : f (restrictElectorate Q (V ∪ T) hWT) = {y} := by
      have hy'' : y ∈ ({z} : Finset A) := by simpa [hz] using hy
      have hyz : y = z := by simpa using hy''
      simp [hz, hyz]
    exact hprop T (by simp [T]) y hy'
  have hQeq : f (restrictElectorate Q (V ∪ T) hWT) = f Q := by
    rw [← restrictElectorate_self Q]
    convert rfl
    · exact hW.symm
    · exact hW.symm
  rw [← hQeq]
  exact hsubset

end SocialChoice
