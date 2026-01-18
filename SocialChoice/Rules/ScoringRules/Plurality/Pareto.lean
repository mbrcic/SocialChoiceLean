import SocialChoice.Axioms.Pareto
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset

theorem plurality_pareto_efficiency : ParetoEfficiency plurality := by
  intro V A _ _ _ P c d hpref hd
  classical
  rcases Classical.choice (inferInstance : Nonempty V) with v0
  let _ := P.pref v0
  have hcd : c ≠ d := by
    exact ne_of_lt (hpref v0)
  have htopcount_d : topCount P d = 0 := by
    unfold topCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    let _ := P.pref v
    have htop : TopRank P v d := (Finset.mem_filter.mp hv).2
    have hdc : Prefers P v d c := htop c hcd
    have hcd' : Prefers P v c d := hpref v
    exact (lt_asymm hdc hcd')
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
  have hnot : d ∉ plurality P := by
    intro hd'
    have hmax : ∀ e : A, topCount P e ≤ topCount P d :=
      (Finset.mem_filter.mp hd').2
    exact (not_lt_of_ge (hmax t)) hlt
  exact hnot hd

end SocialChoice
