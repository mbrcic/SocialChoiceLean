import SocialChoice.Margin
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.ScoringRules.Borda.Condorcet

namespace SocialChoice

lemma CondorcetLoser_not_winner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x : A} (hlose : CondorcetLoser P x) :
    ¬ CondorcetWinner P x := by
  classical
  intro hwin
  rcases hlose with ⟨hlose, ⟨y, hy⟩⟩
  have hxy : margin_pos P x y :=
    (CondorcetWinner_iff_margin_pos P x).mp hwin y (Ne.symm hy)
  have hyx : margin_pos P y x :=
    (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := y) (d := x) (hcd := hy)).1 (hlose y hy)
  exact (margin_pos_asymm (P := P) x y hxy) hyx

theorem black_CondorcetLoser_criterion : CondorcetLoserCriterion black := by
  intro V A _ _ P x hlose
  classical
  by_cases h : ∃ y, CondorcetWinner P y
  · have hxne : x ≠ Classical.choose h := by
      intro hEq
      subst hEq
      exact CondorcetLoser_not_winner (P := P) (x := Classical.choose h) hlose
        (Classical.choose_spec h)
    simp [black, h, hxne]
  · have hborda : black P = borda P := by
      simp [black, h]
    have hxnot : x ∉ borda P := borda_CondorcetLoser_criterion (P := P) (c := x) hlose
    simpa [hborda] using hxnot

end SocialChoice
