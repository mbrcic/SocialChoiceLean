import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

lemma prefers_acyclic {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) : acyclic (fun a b => Prefers P v a b) := by
  intro c hc
  rcases hc with ⟨hne, hchain⟩
  let _ := P.pref v
  have _ : Trans (Prefers P v) (Prefers P v) (Prefers P v) := by
    refine ⟨?trans⟩
    intro a b c hab hbc
    exact lt_trans hab hbc
  have hmem : List.getLast c hne ∈ c := List.getLast_mem hne
  have hrel : Prefers P v (List.getLast c hne) (List.getLast c hne) := by
    exact List.IsChain.rel_cons (a := List.getLast c hne) (l := c)
      (b := List.getLast c hne) hchain hmem
  exact (lt_irrefl (a := List.getLast c hne)) hrel

theorem splitCycle_pareto : ParetoEfficiency splitCycle := by
  intro V A _ _ _ P c d hpref
  classical
  have hdef : splitCycleDefeats P c d := by
    refine ⟨unanimous_margin P c d hpref, ?_⟩
    intro hcyc
    rcases hcyc with ⟨l, hc, hd, hcycle⟩
    have hcd : margin P c d = (Fintype.card V : Int) :=
      unanimous_margin_eq_card P c d hpref
    have hcycle' : cycle (fun a b => ∀ v : V, Prefers P v a b) l := by
      refine cycle_of_cycle_imp ?_ hcycle
      intro a b hab v
      have hle : (Fintype.card V : Int) ≤ margin P a b := by
        simpa [hcd] using hab
      exact unanimous_of_margin_ge_card P a b hle v
    rcases (Classical.choice (inferInstance : Nonempty V)) with v0
    have hcyclev : cycle (fun a b => Prefers P v0 a b) l := by
      refine cycle_of_cycle_imp ?_ hcycle'
      intro a b hab
      exact hab v0
    exact (prefers_acyclic P v0 l) hcyclev
  intro hd
  have hcond : ∀ y, ¬ splitCycleDefeats P y d := (Finset.mem_filter.mp hd).2
  exact (hcond c) hdef

end SocialChoice
