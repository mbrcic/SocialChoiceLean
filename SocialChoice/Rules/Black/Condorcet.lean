import SocialChoice.Margin
import SocialChoice.Rules.Black.Defs

namespace SocialChoice

lemma CondorcetWinner_unique {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x y : A} (hx : CondorcetWinner P x) (hy : CondorcetWinner P y) :
    x = y := by
  classical
  by_contra hne
  have hxy : margin_pos P x y :=
    (CondorcetWinner_iff_margin_pos P x).mp hx y (by simpa [eq_comm] using hne)
  have hyx : margin_pos P y x :=
    (CondorcetWinner_iff_margin_pos P y).mp hy x (Ne.symm hne)
  exact (margin_pos_asymm (P := P) x y hxy) hyx

theorem black_condorcet_consistency : CondorcetConsistency black := by
  intro V A _ _ P x hwin
  classical
  by_cases h : ∃ y, CondorcetWinner P y
  · have hx' : Classical.choose h = x := by
      exact CondorcetWinner_unique (P := P) (hx := Classical.choose_spec h) (hy := hwin)
    simp [black, h, hx']
  · exact (h ⟨x, hwin⟩).elim

end SocialChoice
