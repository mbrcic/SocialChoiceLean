import SocialChoice.Axioms.Monotonicity
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Minimax.Monotonicity
import SocialChoice.Rules.ScoringRules.Borda.Monotonicity

namespace SocialChoice

theorem black_monotonicity : Monotonicity black := by
  intro V A _ _ P P' x hx hLift
  classical
  by_cases hP : ∃ y, CondorcetWinner P y
  · have hxwinP : CondorcetWinner P (Classical.choose hP) := Classical.choose_spec hP
    have hxwinP_pos :
        ∀ y, Classical.choose hP ≠ y → margin_pos P (Classical.choose hP) y :=
      (CondorcetWinner_iff_margin_pos P (Classical.choose hP)).mp hxwinP
    have hx_eq : x = Classical.choose hP := by
      have : x ∈ ({Classical.choose hP} : Finset A) := by
        simpa [black, hP] using hx
      exact Finset.mem_singleton.mp this
    have hxwinP' : CondorcetWinner P' (Classical.choose hP) := by
      apply (CondorcetWinner_iff_margin_pos P' (Classical.choose hP)).mpr
      intro y hy
      have hle : margin P (Classical.choose hP) y ≤ margin P' (Classical.choose hP) y :=
        margin_le_of_simpleLift_other (P := P) (P' := P') (x := x)
          (y := y) (a := Classical.choose hP) hLift (by simpa [hx_eq, eq_comm] using hy)
      have hpos : margin_pos P (Classical.choose hP) y := hxwinP_pos y hy
      have hpos' : 0 < margin P (Classical.choose hP) y := by
        simpa [margin_pos] using hpos
      have hpos'' : 0 < margin P' (Classical.choose hP) y := lt_of_lt_of_le hpos' hle
      simpa [margin_pos] using hpos''
    by_cases hP' : ∃ y, CondorcetWinner P' y
    · have hx_choose : Classical.choose hP' = x := by
        have hx_choose' := CondorcetWinner_unique (P := P')
          (hx := Classical.choose_spec hP') (hy := hxwinP')
        simpa [hx_eq] using hx_choose'
      simp [black, hP', hx_choose]
    · exact (hP' ⟨x, by simpa [hx_eq] using hxwinP'⟩).elim
  · have hx_borda : x ∈ borda P := by
      simpa [black, hP] using hx
    have hx_borda' : x ∈ borda P' :=
      borda_monotonicity (P := P) (P' := P') (x := x) hx_borda hLift
    set x0 : A := x
    have hLift0 : simpleLift P' P x0 := by
      simpa [x0] using hLift
    have hx_borda0 : x0 ∈ borda P := by
      simpa [x0] using hx_borda
    have hx_borda0' : x0 ∈ borda P' := by
      simpa [x0] using hx_borda'
    by_cases hP' : ∃ y, CondorcetWinner P' y
    · have hx_choose : Classical.choose hP' = x0 := by
        by_contra hne
        have hyx : Classical.choose hP' ≠ x0 := by
          simpa [x0] using hne
        have hywinP : CondorcetWinner P (Classical.choose hP') := by
          apply (CondorcetWinner_iff_margin_pos P (Classical.choose hP')).mpr
          intro w hw
          by_cases hwx : w = x0
          · subst hwx
            have hle : margin P' (Classical.choose hP') x0 ≤
                margin P (Classical.choose hP') x0 :=
              margin_le_of_simpleLift_x (P := P) (P' := P') (x := x0)
                (a := Classical.choose hP') hLift0
            have hpos : margin_pos P' (Classical.choose hP') x0 :=
              (CondorcetWinner_iff_margin_pos P' (Classical.choose hP')).mp
                (Classical.choose_spec hP') x0 (by simpa [eq_comm, x0] using hyx)
            have hpos' : 0 < margin P' (Classical.choose hP') x0 := by
              simpa [margin_pos] using hpos
            have hpos'' : 0 < margin P (Classical.choose hP') x0 :=
              lt_of_lt_of_le hpos' hle
            simpa [margin_pos] using hpos''
          · have hEq : margin P (Classical.choose hP') w = margin P' (Classical.choose hP') w :=
              margin_eq_of_simpleLift P P' x0 (Classical.choose hP') w
                (by exact hyx) (by exact hwx) hLift0
            have hpos : margin_pos P' (Classical.choose hP') w :=
              (CondorcetWinner_iff_margin_pos P' (Classical.choose hP')).mp
                (Classical.choose_spec hP') w hw
            simpa [margin_pos, hEq] using hpos
        exact (hP ⟨Classical.choose hP', hywinP⟩).elim
      have : x0 ∈ black P' := by
        simp [black, hP', hx_choose]
      simpa [x0] using this
    · simpa [black, hP', x0] using hx_borda0'

end SocialChoice
