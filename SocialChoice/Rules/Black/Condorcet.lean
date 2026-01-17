import SocialChoice.Margin
import SocialChoice.Rules.Black.Defs

namespace SocialChoice

lemma condorcet_winner_unique {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x y : A} (hx : condorcet_winner P x) (hy : condorcet_winner P y) :
    x = y := by
  classical
  by_contra hne
  have hxy : margin_pos P x y := hx y hne
  have hyx : margin_pos P y x := hy x (by simpa [eq_comm] using hne)
  exact (margin_pos_asymm (P := P) x y hxy) hyx

theorem black_condorcet_criterion : condorcet_criterion black := by
  intro V A _ _ P x hwin
  classical
  by_cases h : ∃ y, condorcet_winner P y
  · have hx' : Classical.choose h = x := by
      exact condorcet_winner_unique (P := P) (hx := Classical.choose_spec h) (hy := hwin)
    simp [black, h, hx']
  · exact (h ⟨x, hwin⟩).elim

end SocialChoice

