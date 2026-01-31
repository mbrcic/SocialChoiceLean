import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.Nanson.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.InformationalBasis

namespace SocialChoice

lemma liftWinners_nansonAux_restrictCandidates_congr
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (n : Nat) (P : Profile V A)
    {p q : A → Prop} [DecidablePred p] [DecidablePred q]
    (h : p = q) :
    liftWinners (nansonAux n {a : A // p a} (restrictCandidates P p)) =
      liftWinners (nansonAux n {a : A // q a} (restrictCandidates P q)) := by
  classical
  cases h
  rename_i instP instQ
  have hinst : instP = instQ := Subsingleton.elim _ _
  cases hinst
  rfl

lemma nansonAux_marginBased {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂] :
    ∀ n : Nat, ∀ (A : Type) [Fintype A] [DecidableEq A],
      ∀ (P₁ : Profile V₁ A) (P₂ : Profile V₂ A),
        (∀ x y : A, margin P₁ x y = margin P₂ x y) →
        nansonAux n A P₁ = nansonAux n A P₂ := by
  intro n
  induction n with
  | zero =>
      intro A _ _ P₁ P₂ _hmargin
      simp [nansonAux]
  | succ n ih =>
      intro A _ _ P₁ P₂ hmargin
      classical
      have hscore :
          ∀ a : A, c2BordaScore P₁ a = c2BordaScore P₂ a :=
        c2BordaScore_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
      by_cases hall₁ : ∀ a : A, c2BordaScore P₁ a = 0
      ·
        have hall₂ : ∀ a : A, c2BordaScore P₂ a = 0 := by
          intro a
          simpa [hscore a] using hall₁ a
        simp [nansonAux, hall₁, hall₂]
      ·
        have hall₂ : ¬ ∀ a : A, c2BordaScore P₂ a = 0 := by
          intro hall₂
          apply hall₁
          intro a
          simpa [hscore a] using hall₂ a
        by_cases hsurv₁ :
          (Finset.univ.filter (fun a => c2BordaScore P₁ a > 0)).Nonempty
        ·
          have hsurv₂ :
              (Finset.univ.filter (fun a => c2BordaScore P₂ a > 0)).Nonempty := by
            rcases hsurv₁ with ⟨a, ha⟩
            refine ⟨a, ?_⟩
            have ha' : c2BordaScore P₁ a > 0 := (Finset.mem_filter.mp ha).2
            have ha'' : c2BordaScore P₂ a > 0 := by
              simpa [hscore a] using ha'
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha''⟩
          let p : A → Prop := fun a => c2BordaScore P₁ a > 0
          let q : A → Prop := fun a => c2BordaScore P₂ a > 0
          have hp : p = q := by
            funext a
            apply propext
            simp [p, q, hscore a]
          have hmargin' :
              ∀ x y : {a : A // p a},
                margin (restrictCandidates P₁ p) x y =
                  margin (restrictCandidates P₂ p) x y := by
            intro x y
            have h1 :=
              margin_eq_margin_restrictCandidates (P := P₁) (p := p) (a := x) (b := y)
            have h2 :=
              margin_eq_margin_restrictCandidates (P := P₂) (p := p) (a := x) (b := y)
            calc
              margin (restrictCandidates P₁ p) x y = margin P₁ x y := by
                simpa using h1.symm
              _ = margin P₂ x y := hmargin x y
              _ = margin (restrictCandidates P₂ p) x y := by
                simpa using h2
          have hrec :
              nansonAux n {a : A // p a} (restrictCandidates P₁ p) =
                nansonAux n {a : A // p a} (restrictCandidates P₂ p) := by
            exact ih (A := {a : A // p a}) (P₁ := restrictCandidates P₁ p)
              (P₂ := restrictCandidates P₂ p) hmargin'
          have hcast :
              liftWinners (nansonAux n {a : A // p a} (restrictCandidates P₂ p)) =
                liftWinners (nansonAux n {a : A // q a} (restrictCandidates P₂ q)) := by
            exact liftWinners_nansonAux_restrictCandidates_congr (n := n) (P := P₂) hp
          have haux₂ :
              nansonAux (Nat.succ n) A P₂ =
                liftWinners (nansonAux n {a : A // q a} (restrictCandidates P₂ q)) := by
            simp [nansonAux, hall₂, hsurv₂, q]
          calc
            nansonAux (Nat.succ n) A P₁ =
                liftWinners (nansonAux n {a : A // p a} (restrictCandidates P₁ p)) := by
                  simp [nansonAux, hall₁, hsurv₁, p]
            _ = liftWinners (nansonAux n {a : A // p a} (restrictCandidates P₂ p)) := by
                  simp [hrec]
            _ = liftWinners (nansonAux n {a : A // q a} (restrictCandidates P₂ q)) := by
                  exact hcast
            _ = nansonAux (Nat.succ n) A P₂ := by
                  symm
                  exact haux₂
        ·
          have hsurv₂ :
              ¬ (Finset.univ.filter (fun a => c2BordaScore P₂ a > 0)).Nonempty := by
            intro hsurv₂
            apply hsurv₁
            rcases hsurv₂ with ⟨a, ha⟩
            refine ⟨a, ?_⟩
            have ha' : c2BordaScore P₂ a > 0 := (Finset.mem_filter.mp ha).2
            have ha'' : c2BordaScore P₁ a > 0 := by
              simpa [hscore a] using ha'
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha''⟩
          simp [nansonAux, hall₁, hall₂, hsurv₁, hsurv₂]

theorem nanson_marginBased : MarginBased nanson := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  simpa [nanson] using
    (nansonAux_marginBased (V₁ := V₁) (V₂ := V₂) (n := Fintype.card A) (A := A)
      (P₁ := P₁) (P₂ := P₂) hmargin)

end SocialChoice
