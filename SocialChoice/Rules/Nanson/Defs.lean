import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

/-!
# Nanson's Rule

Nanson's rule uses C2Borda scores to iteratively eliminate all candidates with
nonpositive scores. If every candidate has C2Borda score 0, all candidates win.
-/

noncomputable def nansonAux {V : Type} [Fintype V]
    (n : Nat) (A : Type) [Fintype A] [DecidableEq A] :
    Profile V A → Finset A :=
  match n with
  | 0 => fun _ => Finset.univ
  | Nat.succ n =>
      fun P => by
        classical
        let score : A → Int := fun a => c2BordaScore P a
        by_cases hall : ∀ a : A, score a = 0
        · exact Finset.univ
        · by_cases hsurv : (Finset.univ.filter (fun a => score a > 0)).Nonempty
          · let P' : Profile V {a : A // score a > 0} :=
              restrictCandidates P (fun a => score a > 0)
            exact liftWinners (nansonAux n {a : A // score a > 0} P')
          · exact Finset.univ

/-- Nanson's rule based on C2Borda scores. -/
noncomputable def nanson : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    exact nansonAux (Fintype.card A) A P

end SocialChoice
