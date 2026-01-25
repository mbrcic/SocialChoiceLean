import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.ScoringRules.Neutrality

namespace SocialChoice

lemma condorcetWinner_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (c : A) :
    CondorcetWinner (permuteCandidates P σ) (σ c) ↔ CondorcetWinner P c := by
  classical
  constructor
  · intro h
    refine (CondorcetWinner_iff_margin_pos P c).2 ?_
    intro d hdc
    have h' :=
      (CondorcetWinner_iff_margin_pos (permuteCandidates P σ) (σ c)).1 h
    have hne : σ c ≠ σ d := by
      intro hEq
      exact hdc (σ.injective hEq)
    have hpos : margin_pos (permuteCandidates P σ) (σ c) (σ d) := h' (σ d) hne
    simpa using
      (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := σ c) (b := σ d)).1 hpos
  · intro h
    refine (CondorcetWinner_iff_margin_pos (permuteCandidates P σ) (σ c)).2 ?_
    intro d hdc
    have h' := (CondorcetWinner_iff_margin_pos P c).1 h
    have hdc' : c ≠ σ.symm d := by
      intro hEq
      have : σ c = d := by
        simpa using congrArg (fun x => σ x) hEq
      exact hdc this
    have hpos : margin_pos P c (σ.symm d) := h' (σ.symm d) hdc'
    have hpos' : margin_pos P (σ.symm (σ c)) (σ.symm d) := by
      simpa using hpos
    simpa using
      (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := σ c) (b := d)).2 hpos'

theorem black_neutral : Neutrality black := by
  intro V A _ _ P σ
  classical
  by_cases h : ∃ x, CondorcetWinner P x
  · have h' : ∃ y, CondorcetWinner (permuteCandidates P σ) y := by
      rcases h with ⟨x, hx⟩
      exact ⟨σ x, (condorcetWinner_permuteCandidates_iff (P := P) (σ := σ) (c := x)).2 hx⟩
    have hchoose : CondorcetWinner P (Classical.choose h) := Classical.choose_spec h
    have hchoose' :
        CondorcetWinner (permuteCandidates P σ) (σ (Classical.choose h)) :=
      (condorcetWinner_permuteCandidates_iff (P := P) (σ := σ) (c := Classical.choose h)).2 hchoose
    have hEq : Classical.choose h' = σ (Classical.choose h) := by
      apply CondorcetWinner_unique (P := permuteCandidates P σ)
      · exact Classical.choose_spec h'
      · exact hchoose'
    simp [black, h, h', permuteWinners, hEq]
  · have h' : ¬ ∃ y, CondorcetWinner (permuteCandidates P σ) y := by
      intro hex
      rcases hex with ⟨y, hy⟩
      have hy' :
          CondorcetWinner (permuteCandidates P σ) (σ (σ.symm y)) := by
        simpa using hy
      have hx : CondorcetWinner P (σ.symm y) :=
        (condorcetWinner_permuteCandidates_iff (P := P) (σ := σ) (c := σ.symm y)).1 hy'
      exact h ⟨σ.symm y, hx⟩
    have hborda :
        permuteWinners σ (borda P) = borda (permuteCandidates P σ) := by
      simpa [borda] using (scoringRule_neutral (score := bordaScore) (P := P) (σ := σ))
    simpa [black, h, h'] using hborda

end SocialChoice
