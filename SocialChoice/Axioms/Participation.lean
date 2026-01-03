import SocialChoice.Profile
import SocialChoice.Axioms.Core

namespace SocialChoice

def PositiveInvolvement (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (ballot : LinearOrder A),
    c ∈ f P → BallotTop ballot c → c ∈ f (addVoter P ballot)

def NegativeInvolvement (f : VotingRule) : Prop :=
  ∀ {V A : Type*} [Fintype V] [Fintype A]
      (P : Profile V A) (c : A) (ballot : LinearOrder A),
    c ∉ f P → BallotBottom ballot c → c ∉ f (addVoter P ballot)

abbrev Electorate (U : Type*) (S : Finset U) := {u // u ∈ S}

instance (U : Type*) [DecidableEq U] (S : Finset U) : Fintype (Electorate U S) := by
  classical
  simpa [Electorate] using (Fintype.subtype S (by intro x; rfl))

def liftVoter {U : Type*} [DecidableEq U] {V : Finset U} (u : U) (v : Electorate U V) :
    Electorate U (insert u V) :=
  ⟨v.1, by simp [v.2]⟩

def newVoter {U : Type*} [DecidableEq U] {V : Finset U} (u : U) (hu : u ∉ V) :
    Electorate U (insert u V) :=
  ⟨u, by simp [hu]⟩

noncomputable def restrictProfile {U A : Type*} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) (S : Finset U) (hS : S ⊆ W) :
    Profile (Electorate U S) A :=
  { pref := fun v => Q.pref ⟨v.1, hS v.2⟩ }

lemma restrictProfile_agrees {U A : Type*} [DecidableEq U] [Fintype A] {W S : Finset U}
    (Q : Profile (Electorate U W) A) (hS : S ⊆ W) (u : U)
    (hSu : insert u S ⊆ W) :
    ∀ v : Electorate U S,
      (restrictProfile Q (insert u S) hSu).pref (liftVoter (u := u) v) =
        (restrictProfile Q S hS).pref v := by
  intro v
  rfl

lemma restrictProfile_self {U A : Type*} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) :
    restrictProfile Q W (by intro x hx; exact hx) = Q := by
  cases Q
  rfl

lemma restrictProfile_eq_of_subset_proof {U A : Type*} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) {S : Finset U} (h₁ h₂ : S ⊆ W) :
    restrictProfile Q S h₁ = restrictProfile Q S h₂ := by
  ext v
  rfl

def UpperSet {A : Type*} [DecidableEq A] (r : LinearOrder A) (S : Finset A) : Prop :=
  ∀ ⦃x y : A⦄, r.lt x y → y ∈ S → x ∈ S

lemma upperSet_mem_of_not_lt {A : Type*} [DecidableEq A]
    {r : LinearOrder A} {S : Finset A} (hS : UpperSet r S)
    {x y : A} (hx : x ∈ S) (hnot : ¬ r.lt x y) : y ∈ S := by
  by_cases hxy : y = x
  · simpa [hxy] using hx
  · have hlt_or_gt : r.lt y x ∨ r.lt x y := lt_or_gt_of_ne hxy
    cases hlt_or_gt with
    | inl hlt => exact hS hlt hx
    | inr hgt => exact (False.elim (hnot hgt))

def ResoluteParticipation (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {U A : Type*} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A) (x y : A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    f P = {x} →
    f Q = {y} →
    ¬ (Q.pref (newVoter (u := u) (V := V) hu)).lt x y

lemma resoluteParticipation_leaving {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) :
    ∀ {U A : Type*} [DecidableEq U] [Fintype A]
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
    ∀ {U A : Type*} [DecidableEq U] [Fintype A] [DecidableEq A]
        (V W : Finset U) (hVW : V ⊆ W)
        (Q : Profile (Electorate U W) A) (S : Finset A) (x : A),
      f (restrictProfile Q V hVW) = {x} →
      x ∈ S →
      (∀ w (hw : w ∈ W \ V),
        UpperSet (Q.pref ⟨w, (Finset.mem_sdiff.mp hw).1⟩) S) →
      f Q ⊆ S := by
  intro U A _ _ _ V W hVW Q S x hx hxS hUpper
  classical
  let T : Finset U := W \ V
  have hTsub : T ⊆ W := by
    simpa [T] using (Finset.sdiff_subset : W \ V ⊆ W)
  have hVunion : ∀ s : Finset U, s ⊆ T → V ∪ s ⊆ W := by
    intro s hs
    exact Finset.union_subset hVW (Finset.Subset.trans hs hTsub)
  have hprop :
      ∀ s : Finset U, ∀ hs : s ⊆ T,
        ∀ y, f (restrictProfile Q (V ∪ s) (hVunion s hs)) = {y} → y ∈ S := by
    intro s hs
    revert hs
    refine Finset.induction_on s ?base ?step
    · intro _ y hy
      have hV : V ∪ (∅ : Finset U) ⊆ W := hVunion ∅ (by simp [T])
      have hEqset : V ∪ (∅ : Finset U) = V := by simp
      cases hEqset
      have hEqprof : restrictProfile Q V hV = restrictProfile Q V hVW := by
        exact restrictProfile_eq_of_subset_proof Q hV hVW
      have hy' : f (restrictProfile Q V hVW) = {y} := by
        simpa [hEqprof] using hy
      have hxy : x = y := by
        have hxy' : ({x} : Finset A) = {y} := by simpa [hx] using hy'
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
      have hEqbig : V ∪ insert a s = Sbig := by
        simpa [Sbig, Ssmall] using (Finset.union_insert (a := a) (s := V) (t := s))
      have hcard_small : (f (restrictProfile Q Ssmall hSsmall)).card = 1 := by
        simpa using (hf (restrictProfile Q Ssmall hSsmall))
      rcases Finset.card_eq_one.mp hcard_small with ⟨x', hx'⟩
      have hx'_mem : x' ∈ S := by
        apply ih hsT x' hx'
      have hagree :
          ∀ v : Electorate U Ssmall,
            (restrictProfile Q Sbig hSbig).pref (liftVoter (u := a) v) =
              (restrictProfile Q Ssmall hSsmall).pref v := by
        intro v
        rfl
      have hy' : f (restrictProfile Q Sbig hSbig) = {y} := by
        cases hEqbig
        have hEqprof :
            restrictProfile Q Sbig (hVunion (insert a s) hs) =
              restrictProfile Q Sbig hSbig := by
          exact restrictProfile_eq_of_subset_proof Q _ _
        simpa [hEqprof] using hy
      have hnot :
          ¬ ((restrictProfile Q Sbig hSbig).pref
              (newVoter (u := a) (V := Ssmall) (by
                have haV : a ∉ V := (Finset.mem_sdiff.mp (by simpa [T] using haT)).2
                simp [Ssmall, haV, ha]))).lt x' y := by
        apply hpart (V := Ssmall) (u := a) ?_ (restrictProfile Q Ssmall hSsmall)
            (restrictProfile Q Sbig hSbig) x' y
        · exact hagree
        · exact hx'
        · exact hy'
        ·
          have haV : a ∉ V := (Finset.mem_sdiff.mp (by simpa [T] using haT)).2
          simpa [Ssmall, haV, ha]
      have hUpper_a : UpperSet (Q.pref ⟨a, haW⟩) S := by
        exact hUpper a (by simpa [T] using haT)
      have hnot' :
          ¬ (Q.pref ⟨a, haW⟩).lt x' y := by
        simpa [restrictProfile, newVoter, Ssmall] using hnot
      exact upperSet_mem_of_not_lt hUpper_a hx'_mem hnot'
  have hW : V ∪ T = W := by
    simpa [T] using (Finset.union_sdiff_of_subset hVW)
  have hWT : V ∪ T ⊆ W := by
    simpa [hW] using (Finset.subset_refl W)
  have hsubset : f (restrictProfile Q (V ∪ T) hWT) ⊆ S := by
    intro y hy
    have hcard : (f (restrictProfile Q (V ∪ T) hWT)).card = 1 := by
      simpa using (hf (restrictProfile Q (V ∪ T) hWT))
    rcases Finset.card_eq_one.mp hcard with ⟨z, hz⟩
    have hy' : f (restrictProfile Q (V ∪ T) hWT) = {y} := by
      have hy'' : y ∈ ({z} : Finset A) := by simpa [hz] using hy
      have hyz : y = z := by simpa using hy''
      simpa [hz, hyz] 
    exact hprop T (by simp [T]) y hy'
  have hQeq : restrictProfile Q (V ∪ T) hWT = Q := by
    cases hW
    have hEq : restrictProfile Q W hWT = restrictProfile Q W (by intro x hx; exact hx) := by
      exact restrictProfile_eq_of_subset_proof Q hWT (by intro x hx; exact hx)
    simpa [hEq] using (restrictProfile_self Q)
  simpa [hQeq] using hsubset

end SocialChoice
