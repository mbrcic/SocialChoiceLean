import SocialChoice.Margin
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.ScoringRules.Borda.Condorcet

namespace SocialChoice

lemma condorcet_loser_not_winner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x : A} (hlose : condorcet_loser P x) :
    ¬ condorcet_winner P x := by
  classical
  intro hwin
  rcases hlose with ⟨hlose, ⟨y, hy⟩⟩
  have hxy : margin_pos P x y := hwin y hy
  have hyx : margin_pos P y x := hlose y (by simpa [eq_comm] using hy)
  exact (margin_pos_asymm (P := P) x y hxy) hyx

theorem black_condorcet_loser_criterion : condorcet_loser_criterion black := by
  intro V A _ _ P x hlose
  classical
  by_cases h : ∃ y, condorcet_winner P y
  · have hxne : x ≠ Classical.choose h := by
      intro hEq
      subst hEq
      exact condorcet_loser_not_winner (P := P) (x := Classical.choose h) hlose
        (Classical.choose_spec h)
    simp [black, h, hxne]
  · have hborda : black P = borda P := by
      simp [black, h]
    have hxnot : x ∉ borda P := borda_condorcet_loser (P := P) (x := x) hlose
    simpa [hborda] using hxnot

end SocialChoice

