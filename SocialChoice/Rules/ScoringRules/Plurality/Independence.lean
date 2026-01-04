import SocialChoice.Axioms.Independence
import SocialChoice.Rules
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset

theorem plurality_independenceOfDominated_nonempty :
    ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
      (P : Profile V A) (c d : A),
        (∀ v : V, Prefers P v c d) →
          liftWinners (plurality (restrictCandidates P (fun a => a ≠ d))) = plurality P := by
  intro V A _ _ _ _ P c d hpref
  classical
  rcases Classical.choice (inferInstance : Nonempty V) with v0
  let _ := P.pref v0
  have hcd : c ≠ d := by
    exact ne_of_lt (hpref v0)
  have hnot_top_d : ∀ v : V, ¬ TopRank P v d := by
    intro v htop
    let _ := P.pref v
    have hdc : Prefers P v d c := htop c hcd
    have hcd' : Prefers P v c d := hpref v
    exact (lt_asymm hdc hcd')
  let P' := restrictCandidates P (fun a => a ≠ d)
  have htopcount_d : topCount P d = 0 := by
    unfold topCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have htop : TopRank P v d := (Finset.mem_filter.mp hv).2
    exact (hnot_top_d v htop)
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  let t : A := (Finset.univ.min' hA)
  have htopt : TopRank P v0 t := by
    intro a ha
    have hleast : IsLeast (↑(Finset.univ : Finset A)) t :=
      Finset.isLeast_min' (s := (Finset.univ : Finset A)) hA
    have hle : t ≤ a := hleast.2 (by simp)
    have hlt : t < a := lt_of_le_of_ne hle (by simpa [eq_comm] using ha)
    simpa [Prefers] using hlt
  have hv0 : v0 ∈ votersTop P t := by
    simp [votersTop, htopt]
  have hpos : 0 < topCount P t := by
    unfold topCount
    exact Finset.card_pos.mpr ⟨v0, hv0⟩
  have hlt : topCount P d < topCount P t := by
    simpa [htopcount_d] using hpos
  have hnot_winner : d ∉ plurality P := by
    intro hd
    have hmax : ∀ e : A, topCount P e ≤ topCount P d :=
      (Finset.mem_filter.mp hd).2
    exact (not_lt_of_ge (hmax t)) hlt
  have topRank_restrict_iff (v : V) (a : A) (hne : a ≠ d) :
      TopRank P' v ⟨a, hne⟩ ↔ TopRank P v a := by
    constructor
    · intro htop b hb
      by_cases hbd : b = d
      · by_contra hnot
        have hda : Prefers P v d a := by
          let _ := P.pref v
          have htrich := lt_trichotomy (a := a) (b := d)
          cases htrich with
          | inl hlt => exact (hnot (by simpa [hbd] using hlt)).elim
          | inr hrest =>
              cases hrest with
              | inl hEq =>
                  exact (hb (by simpa [hbd] using hEq.symm)).elim
              | inr hlt => exact hlt
        have htop_d : TopRank P v d := by
          intro b hb'
          by_cases hba : b = a
          · subst hba
            exact hda
          · have hne' : b ≠ d := by
              intro hbd'
              exact hb' hbd'
            have hab : Prefers P v a b := by
              have hne'' : (⟨b, hne'⟩ : {x : A // x ≠ d}) ≠ ⟨a, hne⟩ := by
                intro hEq
                apply hba
                exact congrArg Subtype.val hEq
              have hab' := htop ⟨b, hne'⟩ hne''
              simpa [P', Prefers, restrictCandidates, restrictBallot] using hab'
            let _ := P.pref v
            exact lt_trans hda hab
        exact (hnot_top_d v htop_d)
      · have hne' : (⟨b, hbd⟩ : {x : A // x ≠ d}) ≠ ⟨a, hne⟩ := by
          intro hEq
          apply hb
          exact congrArg Subtype.val hEq
        have hab' := htop ⟨b, hbd⟩ hne'
        simpa [P', Prefers, restrictCandidates, restrictBallot] using hab'
    · intro htop b hb
      have hb' : (b : A) ≠ a := by
        intro hEq
        apply hb
        ext
        simpa using hEq
      have hab : Prefers P v a b := htop b hb'
      simpa [P', Prefers, restrictCandidates, restrictBallot] using hab
  have topCount_restrict (a : A) (hne : a ≠ d) :
      topCount P' ⟨a, hne⟩ = topCount P a := by
    unfold topCount
    apply congrArg Finset.card
    ext v
    simp [votersTop, topRank_restrict_iff v a hne]
  apply Finset.ext
  intro a
  by_cases had : a = d
  · subst had
    have : a ∉ liftWinners (plurality P') := by
      simp [liftWinners, P']
    constructor
    · intro ha
      exact (this ha).elim
    · intro ha
      exact (hnot_winner ha).elim
  · have hne : a ≠ d := had
    constructor
    · intro ha
      have ha' : ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ plurality P' := by
        simpa [liftWinners, P'] using ha
      rcases ha' with ⟨hne', ha'⟩
      have ha'' : (⟨a, hne⟩ : {x : A // x ≠ d}) ∈ plurality P' := by
        simpa using ha'
      have hmax : ∀ e : {x : A // x ≠ d}, topCount P' e ≤ topCount P' ⟨a, hne⟩ :=
        (Finset.mem_filter.mp ha'').2
      have hmax' : ∀ e : A, topCount P e ≤ topCount P a := by
        intro e
        by_cases hed : e = d
        · subst hed
          simp [htopcount_d]
        · have hne' : e ≠ d := hed
          have hmax'' := hmax ⟨e, hne'⟩
          simpa [topCount_restrict e hne', topCount_restrict a hne] using hmax''
      have ha''' : a ∈ (Finset.univ.filter
          (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
        exact mem_filter.mpr ⟨mem_univ _, hmax'⟩
      simpa [plurality] using ha'''
    · intro ha
      have ha' : a ∈ (Finset.univ.filter
          (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
        simpa [plurality] using ha
      have hmax : ∀ e : {x : A // x ≠ d}, topCount P' e ≤ topCount P' ⟨a, hne⟩ := by
        intro e
        have hmax' : topCount P e ≤ topCount P a := (mem_filter.mp ha').2 e
        simpa [topCount_restrict e e.2, topCount_restrict a hne] using hmax'
      have ha'' : (⟨a, hne⟩ : {x : A // x ≠ d}) ∈ plurality P' := by
        exact mem_filter.mpr ⟨mem_univ _, hmax⟩
      have ha''' :
          ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ plurality P' := ⟨hne, ha''⟩
      simpa [liftWinners, P'] using ha'''

end SocialChoice
