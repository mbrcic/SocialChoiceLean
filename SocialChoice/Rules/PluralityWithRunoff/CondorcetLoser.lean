import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset

lemma mem_secondPluralitySet_not_mem {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A) {x : A} (hx : x ∈ secondPluralitySet P S) :
    x ∉ S := by
  classical
  by_cases hR : (Finset.univ.filter (fun c => c ∉ S)).Nonempty
  · have hx' :
      x ∈ (Finset.univ.filter (fun c => c ∉ S)).filter
        (fun c => topCount P c =
          ((Finset.univ.filter (fun c => c ∉ S)).image (fun c => topCount P c)).max' (by
            simpa [Finset.Nonempty] using hR.image (fun c => topCount P c))) := by
      have hx'' :
          x ∈ Finset.univ.filter (fun c => c ∉ S) ∧
            topCount P x =
              ((Finset.univ.filter (fun c => c ∉ S)).image (fun c => topCount P c)).max' (by
                simpa [Finset.Nonempty] using hR.image (fun c => topCount P c)) := by
        simpa [secondPluralitySet, hR] using hx
      exact Finset.mem_filter.mpr hx''
    have hxR : x ∈ Finset.univ.filter (fun c => c ∉ S) := (Finset.mem_filter.mp hx').1
    exact (Finset.mem_filter.mp hxR).2
  · have : secondPluralitySet P S = ∅ := by
      simp [secondPluralitySet, hR]
    simp [this] at hx

lemma mem_pluralityWithRunoffPairs_card {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {s : Finset A} (hs : s ∈ pluralityWithRunoffPairs P) : s.card = 2 := by
  classical
  let S := plurality P
  by_cases hS : S.card ≥ 2
  · have hs' : s ∈ S.powersetCard 2 := by
      simpa [pluralityWithRunoffPairs, hS, S] using hs
    exact (Finset.mem_powersetCard.mp hs').2
  · have hs' :
        s ∈ (S.product (secondPluralitySet P S)).image
          (fun p => ({p.1, p.2} : Finset A)) := by
      simpa [pluralityWithRunoffPairs, hS, S] using hs
    rcases Finset.mem_image.mp hs' with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hp2_notin : p.2 ∉ S := mem_secondPluralitySet_not_mem (P := P) (S := S) hp2
    have hp1_ne_hp2 : p.1 ≠ p.2 := by
      intro hEq
      apply hp2_notin
      simpa [hEq] using hp1
    exact Finset.card_eq_two.mpr ⟨p.1, p.2, hp1_ne_hp2, rfl⟩

theorem plurality_with_runoff_CondorcetLoser_criterion :
    CondorcetLoserCriterion pluralityWithRunoff := by
  intro V A _ _ P x hloser
  classical
  by_cases hcard : Fintype.card A ≤ 1
  · rcases hloser.2 with ⟨y, hxy⟩
    have hforall : ∀ a b : A, a = b := (Fintype.card_le_one_iff).1 hcard
    exfalso
    exact hxy (hforall y x)
  · by_contra hxmem
    have hxmem' :
        ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P x y := by
      simpa [pluralityWithRunoff, hcard] using hxmem
    rcases hxmem' with ⟨y, hpair, hnonneg⟩
    have hcardpair : ({x, y} : Finset A).card = 2 :=
      mem_pluralityWithRunoffPairs_card (P := P) hpair
    have hxy : x ≠ y := by
      by_contra hxy
      simp [hxy] at hcardpair
    have hpos : margin_pos P y x :=
      (CondorcetLoser_iff_margin_pos P x).mp hloser |>.1 y (by simpa [eq_comm] using hxy)
    have hneg : margin P x y < 0 := by
      have hpos' : 0 < margin P y x := by
        simpa [margin_pos] using hpos
      have hskew : margin P x y = - margin P y x := by
        simpa [skew_symmetric] using (margin_antisymmetric (P := P)) x y
      linarith
    exact (not_lt_of_ge hnonneg) hneg

end SocialChoice
