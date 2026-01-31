import SocialChoice.Axioms.Condorcet
import SocialChoice.Margin
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

lemma copelandPairScore2_lt_condorcet_self {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hwin : CondorcetWinner P c) {a : A} (ha : a ≠ c) :
    copelandPairScore2 (margin P a c) < copelandPairScore2 (margin P c c) := by
  have hpos : margin_pos P c a :=
    (CondorcetWinner_iff_margin_pos P c).1 hwin a (by simpa [eq_comm] using ha)
  have hpos' : 0 < margin P c a := by
    simpa [margin_pos] using hpos
  have hskew : margin P a c = - margin P c a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a c
  have hneg : margin P a c < 0 := by linarith
  have hnotpos : ¬ margin P a c > 0 := by
    exact not_lt_of_ge (le_of_lt hneg)
  have hne : margin P a c ≠ 0 := ne_of_lt hneg
  have hleft : copelandPairScore2 (margin P a c) = 0 := by
    simp [copelandPairScore2, hnotpos, hne]
  have hright : copelandPairScore2 (margin P c c) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  simp [hleft, hright]

lemma copelandPairScore2_le_condorcet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hwin : CondorcetWinner P c) (a b : A) :
    copelandPairScore2 (margin P a b) ≤ copelandPairScore2 (margin P c b) := by
  classical
  by_cases hbc : b = c
  · by_cases hac : a = c
    · subst hac
      simp [hbc, copelandPairScore2, self_margin_zero]
    · have hlt :
        copelandPairScore2 (margin P a c) < copelandPairScore2 (margin P c c) :=
        copelandPairScore2_lt_condorcet_self (P := P) (hwin := hwin) hac
      have hle : copelandPairScore2 (margin P a c) ≤ copelandPairScore2 (margin P c c) :=
        le_of_lt hlt
      simpa [hbc] using hle
  · have hpos : margin_pos P c b :=
      (CondorcetWinner_iff_margin_pos P c).1 hwin b (by simpa [eq_comm] using hbc)
    have hpos' : margin P c b > 0 := by
      simpa [margin_pos] using hpos
    have hscore_c : copelandPairScore2 (margin P c b) = 2 := by
      simp [copelandPairScore2, hpos']
    have hle : copelandPairScore2 (margin P a b) ≤ 2 :=
      copelandPairScore2_le_two _
    simpa [hscore_c] using hle

lemma copelandScore2_le_condorcet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hwin : CondorcetWinner P c) (a : A) :
    copelandScore2 P a ≤ copelandScore2 P c := by
  classical
  refine Finset.sum_le_sum ?_
  intro b hb
  exact copelandPairScore2_le_condorcet (P := P) (hwin := hwin) a b

lemma copelandScore2_lt_condorcet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hwin : CondorcetWinner P c) {a : A} (ha : a ≠ c) :
    copelandScore2 P a < copelandScore2 P c := by
  classical
  refine Finset.sum_lt_sum ?_ ?_
  · intro b hb
    exact copelandPairScore2_le_condorcet (P := P) (hwin := hwin) a b
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    exact copelandPairScore2_lt_condorcet_self (P := P) (hwin := hwin) ha

/-- Copeland satisfies the Condorcet criterion. -/
theorem copeland_condorcet_consistency : CondorcetConsistency copeland := by
  intro V A _ _ P c hwin
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, Finset.mem_univ c⟩
  have hnonempty : Nonempty A := ⟨c⟩
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
  have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 P a)
  have hmem : copelandScore2 P c ∈ scores := by
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  have hmax_le : Finset.max' scores hScores ≤ copelandScore2 P c := by
    refine (Finset.max'_le_iff _ _).2 ?_
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    exact copelandScore2_le_condorcet (P := P) (hwin := hwin) a
  have hle_max : copelandScore2 P c ≤ Finset.max' scores hScores :=
    Finset.le_max' _ _ hmem
  have hmax_eq : Finset.max' scores hScores = copelandScore2 P c :=
    le_antisymm hmax_le hle_max
  have hmax_eq' : copelandMaxScore2 (V := V) (A := A) P = copelandScore2 P c := by
    simp [copelandMaxScore2, hA, scores, hmax_eq]

  have hset :
      copeland P =
        Finset.univ.filter (fun a => copelandScore2 P a = copelandScore2 P c) := by
    simp [copeland, hnonempty, hmax_eq']

  have hmem_c : c ∈ copeland P := by
    simp [hset]

  have hsubset : copeland P ⊆ {c} := by
    intro x hx
    have hx' : copelandScore2 P x = copelandScore2 P c := by
      have : x ∈ Finset.univ.filter (fun a => copelandScore2 P a = copelandScore2 P c) :=
        by simpa [hset] using hx
      exact (Finset.mem_filter.mp this).2
    by_cases hxc : x = c
    · simp [hxc]
    · have hlt := copelandScore2_lt_condorcet (P := P) (hwin := hwin) hxc
      have : False := by linarith
      cases this

  apply Finset.ext
  intro x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have : x = c := by simpa using hx
    subst this
    simpa using hmem_c

end SocialChoice
