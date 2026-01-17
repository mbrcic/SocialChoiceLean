import SocialChoice.Axioms.Monotonicity
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Minimax.Monotonicity
import SocialChoice.Rules.ScoringRules.Borda.Monotonicity

namespace SocialChoice

theorem black_monotonicity : Monotonicity black := by
  intro V A _ _ P P' x hx hLift
  classical
  by_cases hP : ∃ y, condorcet_winner P y
  · have hxwinP : condorcet_winner P (Classical.choose hP) := Classical.choose_spec hP
    have hx_eq : x = Classical.choose hP := by
      have : x ∈ ({Classical.choose hP} : Finset A) := by
        simpa [black, hP] using hx
      exact Finset.mem_singleton.mp this
    subst hx_eq
    have hxwinP' : condorcet_winner P' x := by
      intro y hy
      have hle : margin P x y ≤ margin P' x y :=
        margin_le_of_simpleLift_other (P := P) (P' := P') (x := x) (y := y) (a := x) hLift hy
      exact lt_of_lt_of_le (hxwinP y hy) hle
    by_cases hP' : ∃ y, condorcet_winner P' y
    · have hx_choose : Classical.choose hP' = x := by
        exact condorcet_winner_unique (P := P')
          (hx := Classical.choose_spec hP') (hy := hxwinP')
      simpa [black, hP', hx_choose]
    · exact (hP' ⟨x, hxwinP'⟩).elim
  · have hx_borda : x ∈ borda P := by
      simpa [black, hP] using hx
    have hx_borda' : x ∈ borda P' :=
      borda_monotonicity (P := P) (P' := P') (x := x) hx_borda hLift
    by_cases hP' : ∃ y, condorcet_winner P' y
    · have hx_choose : Classical.choose hP' = x := by
        by_contra hne
        have hne' : Classical.choose hP' ≠ x := hne
        have hnotP : ¬ condorcet_winner P (Classical.choose hP') := by
          intro hcw
          exact hP ⟨Classical.choose hP', hcw⟩
        have hnotP' : ∃ z, z ≠ Classical.choose hP' ∧
            ¬ margin_pos P (Classical.choose hP') z := by
          by_contra hforall
          have hforall' :
              ∀ z, z ≠ Classical.choose hP' → margin_pos P (Classical.choose hP') z := by
            intro z hz
            by_contra hnm
            exact hforall ⟨z, hz, hnm⟩
          exact hnotP (by intro z hz; exact hforall' z hz)
        rcases hnotP' with ⟨z, hz, hnm⟩
        have hnm' : ¬ margin_pos P' (Classical.choose hP') z := by
          by_cases hzx : z = x
          · subst hzx
            have hle : margin P' (Classical.choose hP') x ≤
                margin P (Classical.choose hP') x :=
              margin_le_of_simpleLift_x (P := P) (P' := P') (x := x) (a := Classical.choose hP')
                hLift
            exact fun hpos =>
              hnm (lt_of_lt_of_le hpos hle)
          · have hEq : margin P (Classical.choose hP') z = margin P' (Classical.choose hP') z :=
              margin_eq_of_simpleLift P P' x (Classical.choose hP') z
                (by exact hne') (by exact hzx) hLift
            exact fun hpos => hnm (by simpa [hEq] using hpos)
        exact hnm' (Classical.choose_spec hP')
      simpa [black, hP', hx_choose]
    · simpa [black, hP'] using hx_borda'

end SocialChoice

