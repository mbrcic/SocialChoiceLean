import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset

lemma exists_pos_c2BordaScore_of_neg {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hneg : c2BordaScore P c < 0) :
    ∃ d, 0 < c2BordaScore P d := by
  classical
  by_contra hno
  have hnonpos : ∀ d, c2BordaScore P d ≤ 0 := by
    intro d
    by_contra hdpos
    exact hno ⟨d, lt_of_not_ge hdpos⟩
  have hsum :
      (Finset.univ : Finset A).sum (fun d => c2BordaScore P d) =
        (Finset.univ.erase c).sum (fun d => c2BordaScore P d) + c2BordaScore P c := by
    have hsum' :=
      Finset.sum_erase_add (s := (Finset.univ : Finset A))
        (f := fun d => c2BordaScore P d) (a := c) (by exact Finset.mem_univ c)
    exact hsum'.symm
  have hsum_rest_nonpos :
      (Finset.univ.erase c).sum (fun d => c2BordaScore P d) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro d hd
    exact hnonpos d
  have hsum_lt :
      (Finset.univ : Finset A).sum (fun d => c2BordaScore P d) < 0 := by
    have hlt :
        (Finset.univ.erase c).sum (fun d => c2BordaScore P d) + c2BordaScore P c < 0 :=
      add_lt_of_le_of_neg hsum_rest_nonpos hneg
    rw [hsum]
    exact hlt
  have hsum_zero := c2BordaScore_sum_zero (P := P)
  have hsum_lt' := hsum_lt
  rw [hsum_zero] at hsum_lt'
  exact (lt_irrefl 0 hsum_lt')

lemma not_mem_liftWinners_of_not_pred {A : Type} {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {c : A} (hc : ¬ p c) :
    c ∉ liftWinners s := by
  classical
  intro hc'
  rcases Finset.mem_image.mp hc' with ⟨x, hx, hxc⟩
  have : p c := by
    simpa [hxc] using x.property
  exact hc this

theorem nanson_condorcet_loser_criterion : condorcet_loser_criterion nanson := by
  intro V A _ _ P c hloser
  classical
  letI : DecidableEq A := Classical.decEq A
  have hneg : c2BordaScore P c < 0 :=
    c2BordaScore_neg_of_condorcet_loser (P := P) (x := c) hloser
  have hpos_ex : ∃ d, 0 < c2BordaScore P d :=
    exists_pos_c2BordaScore_of_neg (P := P) (c := c) hneg
  have hall : ¬ ∀ a : A, c2BordaScore P a = 0 := by
    intro hall
    have h0 := hall c
    exact (ne_of_lt hneg) h0
  let p : A → Prop := fun a => c2BordaScore P a > 0
  have hsurv : (Finset.univ.filter (fun a => p a)).Nonempty := by
    rcases hpos_ex with ⟨d, hdpos⟩
    exact ⟨d, by simp [p, hdpos]⟩
  have hcnotp : ¬ p c := by
    dsimp [p]
    exact not_lt_of_ge (le_of_lt hneg)
  have hcard_pos : 0 < Fintype.card A := by
    rcases hloser.2 with ⟨y, _hy⟩
    exact Fintype.card_pos_iff.mpr ⟨y⟩
  have hcard_ne_zero : Fintype.card A ≠ 0 := ne_of_gt hcard_pos
  simp [nanson]
  cases hcardA : Fintype.card A with
  | zero =>
      exact (hcard_ne_zero hcardA).elim
  | succ n =>
      change c ∉ nansonAux (Nat.succ n) A P
      have hnot :
          c ∉ liftWinners (nansonAux n {a : A // p a} (restrictCandidates P p)) :=
        not_mem_liftWinners_of_not_pred (p := p)
          (s := nansonAux n {a : A // p a} (restrictCandidates P p)) hcnotp
      simpa [nansonAux, hall, hsurv, p] using hnot

end SocialChoice
