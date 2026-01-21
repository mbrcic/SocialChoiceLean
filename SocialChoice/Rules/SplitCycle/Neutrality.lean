import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

lemma splitCycleDefeats_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (x y : A) :
    splitCycleDefeats (permuteCandidates P σ) (σ x) (σ y) ↔ splitCycleDefeats P x y := by
  classical
  constructor
  · intro h
    rcases h with ⟨hpos, hnocycle⟩
    have hpos' : margin_pos P x y := by
      simpa using
        (margin_pos_permuteCandidates_iff (P := P) (σ := σ)
          (a := σ x) (b := σ y)).1 hpos
    refine ⟨hpos', ?_⟩
    intro hcyc
    rcases hcyc with ⟨c, hx, hy, hcycle⟩
    let Rσ : A → A → Prop :=
      fun a b =>
        margin (permuteCandidates P σ) (σ x) (σ y) ≤
          margin (permuteCandidates P σ) a b
    have hcycle' : cycle Rσ (c.map σ) := by
      have hcycle_pre : cycle (fun a b => Rσ (σ a) (σ b)) c := by
        simpa [Rσ] using hcycle
      exact cycle_map (f := σ) (P := Rσ) hcycle_pre
    have hx' : σ x ∈ c.map σ := by
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hy' : σ y ∈ c.map σ := by
      exact List.mem_map.mpr ⟨y, hy, rfl⟩
    exact hnocycle ⟨c.map σ, hx', hy', hcycle'⟩
  · intro h
    rcases h with ⟨hpos, hnocycle⟩
    have hpos' : margin_pos (permuteCandidates P σ) (σ x) (σ y) := by
      simpa using
        (margin_pos_permuteCandidates_iff (P := P) (σ := σ)
          (a := σ x) (b := σ y)).2 (by simpa using hpos)
    refine ⟨hpos', ?_⟩
    intro hcyc
    rcases hcyc with ⟨c, hx, hy, hcycle⟩
    let R : A → A → Prop :=
      fun a b => margin P x y ≤ margin P a b
    let Rσ : A → A → Prop :=
      fun a b =>
        margin (permuteCandidates P σ) (σ x) (σ y) ≤
          margin (permuteCandidates P σ) a b
    have hcycle' : cycle R (c.map σ.symm) := by
      have hcycle_pre : cycle (fun a b => R (σ.symm a) (σ.symm b)) c := by
        simpa [R, Rσ] using hcycle
      exact cycle_map (f := σ.symm) (P := R) hcycle_pre
    have hx' : x ∈ c.map σ.symm := by
      exact List.mem_map.mpr ⟨σ x, hx, by simp⟩
    have hy' : y ∈ c.map σ.symm := by
      exact List.mem_map.mpr ⟨σ y, hy, by simp⟩
    exact hnocycle ⟨c.map σ.symm, hx', hy', hcycle'⟩

lemma splitCycleDefeats_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (a b : B) :
    splitCycleDefeats (relabelProfile P e) a b ↔
      splitCycleDefeats P (e.symm a) (e.symm b) := by
  classical
  constructor
  · intro h
    rcases h with ⟨hpos, hnocycle⟩
    have hpos' : margin_pos P (e.symm a) (e.symm b) := by
      simpa using
        (margin_pos_relabelProfile_iff (P := P) (e := e) (a := a) (b := b)).1 hpos
    refine ⟨hpos', ?_⟩
    intro hcyc
    rcases hcyc with ⟨c, ha, hb, hcycle⟩
    let R : B → B → Prop :=
      fun u v =>
        margin (relabelProfile P e) a b ≤ margin (relabelProfile P e) u v
    have hcycle_pre : cycle (fun u v => R (e u) (e v)) c := by
      simpa [R] using hcycle
    have hcycle' : cycle R (c.map e) := by
      exact cycle_map (P := R) (f := e) hcycle_pre
    have ha' : a ∈ c.map e := by
      exact List.mem_map.mpr ⟨e.symm a, ha, by simp⟩
    have hb' : b ∈ c.map e := by
      exact List.mem_map.mpr ⟨e.symm b, hb, by simp⟩
    exact hnocycle ⟨c.map e, ha', hb', hcycle'⟩
  · intro h
    rcases h with ⟨hpos, hnocycle⟩
    have hpos' : margin_pos (relabelProfile P e) a b := by
      simpa using
        (margin_pos_relabelProfile_iff (P := P) (e := e) (a := a) (b := b)).2 hpos
    refine ⟨hpos', ?_⟩
    intro hcyc
    rcases hcyc with ⟨c, ha, hb, hcycle⟩
    let R : A → A → Prop :=
      fun u v => margin P (e.symm a) (e.symm b) ≤ margin P u v
    let R' : B → B → Prop :=
      fun u v =>
        margin (relabelProfile P e) a b ≤ margin (relabelProfile P e) u v
    have hcycle_pre : cycle (fun u v => R (e.symm u) (e.symm v)) c := by
      simpa [R, R'] using hcycle
    have hcycle' : cycle R (c.map e.symm) := by
      exact cycle_map (P := R) (f := e.symm) hcycle_pre
    have ha' : e.symm a ∈ c.map e.symm := by
      exact List.mem_map.mpr ⟨a, ha, by simp⟩
    have hb' : e.symm b ∈ c.map e.symm := by
      exact List.mem_map.mpr ⟨b, hb, by simp⟩
    exact hnocycle ⟨c.map e.symm, ha', hb', hcycle'⟩

theorem splitCycle_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) :
    splitCycle (relabelProfile P e) = (splitCycle P).map e.toEmbedding := by
  classical
  apply Finset.ext
  intro b
  constructor
  · intro hb
    have hb_cond : ∀ y, ¬ splitCycleDefeats (relabelProfile P e) y b :=
      (Finset.mem_filter.mp hb).2
    have hmem : e.symm b ∈ splitCycle P := by
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      intro y
      have hiff :
          splitCycleDefeats (relabelProfile P e) (e y) b ↔
            splitCycleDefeats P y (e.symm b) := by
        simpa using
          (splitCycleDefeats_relabelProfile (P := P) (e := e) (a := e y) (b := b))
      intro hy
      exact (hb_cond (e y)) (hiff.mpr hy)
    exact Finset.mem_map.mpr ⟨e.symm b, hmem, by simp⟩
  · intro hb
    rcases Finset.mem_map.mp hb with ⟨a, ha, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp, ?_⟩
    have ha_cond : ∀ y, ¬ splitCycleDefeats P y a := (Finset.mem_filter.mp ha).2
    intro y
    have hiff :
        splitCycleDefeats (relabelProfile P e) y (e a) ↔
          splitCycleDefeats P (e.symm y) a := by
      simpa using
        (splitCycleDefeats_relabelProfile (P := P) (e := e) (a := y) (b := e a))
    intro hy
    exact (ha_cond (e.symm y)) (hiff.mp hy)

lemma mem_splitCycle_relabelProfile_iff {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (b : B) :
    b ∈ splitCycle (relabelProfile P e) ↔ e.symm b ∈ splitCycle P := by
  classical
  constructor
  · intro hb
    have hb' : b ∈ (splitCycle P).map e.toEmbedding := by
      simpa [splitCycle_relabelProfile (P := P) (e := e)] using hb
    rcases Finset.mem_map.mp hb' with ⟨a, ha, hab⟩
    have ha' : a = e.symm b := by
      simpa using congrArg e.symm hab
    simpa [ha'] using ha
  · intro hb
    have hb' : b ∈ (splitCycle P).map e.toEmbedding := by
      exact Finset.mem_map.mpr ⟨e.symm b, hb, by simp⟩
    simpa [splitCycle_relabelProfile (P := P) (e := e)] using hb'

theorem split_cycle_neutrality : Neutrality splitCycle := by
  intro V A _ _ P σ
  classical
  apply Finset.ext
  intro c
  constructor
  · intro hc
    have hc' := hc
    dsimp [permuteWinners] at hc'
    rcases Finset.mem_map.mp hc' with ⟨a, ha, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp, ?_⟩
    intro y
    have ha_cond : ∀ y, ¬ splitCycleDefeats P y a := (Finset.mem_filter.mp ha).2
    have hiff :
        splitCycleDefeats (permuteCandidates P σ) y (σ a) ↔
          splitCycleDefeats P (σ.symm y) a := by
      simpa using (splitCycleDefeats_permuteCandidates (P := P) (σ := σ)
        (x := σ.symm y) (y := a))
    intro hy
    exact (ha_cond (σ.symm y)) (hiff.mp hy)
  · intro hc
    have hc_cond : ∀ y, ¬ splitCycleDefeats (permuteCandidates P σ) y c :=
      (Finset.mem_filter.mp hc).2
    have hmem : σ.symm c ∈ splitCycle P := by
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      intro y
      have hiff :
          splitCycleDefeats (permuteCandidates P σ) (σ y) c ↔
            splitCycleDefeats P y (σ.symm c) := by
        simpa using (splitCycleDefeats_permuteCandidates (P := P) (σ := σ)
          (x := y) (y := σ.symm c))
      intro hy
      exact (hc_cond (σ y)) (hiff.mpr hy)
    have : c ∈ (splitCycle P).map σ.toEmbedding := by
      exact Finset.mem_map.mpr ⟨σ.symm c, hmem, by simp⟩
    simpa [permuteWinners] using this

end SocialChoice
