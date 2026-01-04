import Mathlib.Tactic
import SocialChoice.Axioms.Reinforcement
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

lemma scoreCandidate_unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P₁ : Profile V A) (P₂ : Profile W A) (score : Nat → Int) (c : A) :
    scoreCandidate (unionProfiles P₁ P₂) score c =
      scoreCandidate P₁ score c + scoreCandidate P₂ score c := by
  classical
  unfold scoreCandidate
  simpa [unionProfiles] using
    (Fintype.sum_sum_type
      (f := fun v : V ⊕ W => score (rank ((unionProfiles P₁ P₂).pref v) c)))

theorem scoringRule_reinforcement (score : Nat → Nat → Int) :
    Reinforcement (scoringRule score) := by
  intro V W A _ _ _ _ P₁ P₂ hnonempty
  classical
  rcases hnonempty with ⟨x, hx⟩
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
  have hx1 : x ∈ scoringWinners P₁ scoreFun := by
    simpa [scoringRule, scoreFun] using (Finset.mem_inter.mp hx).1
  have hx2 : x ∈ scoringWinners P₂ scoreFun := by
    simpa [scoringRule, scoreFun] using (Finset.mem_inter.mp hx).2
  have hA : (Finset.univ : Finset A).Nonempty := ⟨x, by simp⟩
  let scoreSet₁ : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate P₁ scoreFun c))
  let max₁ : Int :=
    scoreSet₁.max' (by
      simpa [scoreSet₁, Finset.Nonempty] using hA)
  let scoreSet₂ : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate P₂ scoreFun c))
  let max₂ : Int :=
    scoreSet₂.max' (by
      simpa [scoreSet₂, Finset.Nonempty] using hA)
  have hx1' : scoreCandidate P₁ scoreFun x = max₁ := by
    simpa [scoringWinners, hA, scoreSet₁, max₁] using hx1
  have hx2' : scoreCandidate P₂ scoreFun x = max₂ := by
    simpa [scoringWinners, hA, scoreSet₂, max₂] using hx2
  have hle1 : ∀ c, scoreCandidate P₁ scoreFun c ≤ max₁ := by
    intro c
    have hmem :
        scoreCandidate P₁ scoreFun c ∈ scoreSet₁ := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    exact Finset.le_max' scoreSet₁ (scoreCandidate P₁ scoreFun c) hmem
  have hle2 : ∀ c, scoreCandidate P₂ scoreFun c ≤ max₂ := by
    intro c
    have hmem :
        scoreCandidate P₂ scoreFun c ∈ scoreSet₂ := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    exact Finset.le_max' scoreSet₂ (scoreCandidate P₂ scoreFun c) hmem
  have hsum_x :
      scoreCandidate (unionProfiles P₁ P₂) scoreFun x = max₁ + max₂ := by
    calc
      scoreCandidate (unionProfiles P₁ P₂) scoreFun x =
          scoreCandidate P₁ scoreFun x + scoreCandidate P₂ scoreFun x := by
            simpa using
              (scoreCandidate_unionProfiles (P₁ := P₁) (P₂ := P₂) (score := scoreFun) (c := x))
      _ = max₁ + max₂ := by
            simpa [hx1', hx2']
  have hle_union : ∀ c,
      scoreCandidate (unionProfiles P₁ P₂) scoreFun c ≤ max₁ + max₂ := by
    intro c
    calc
      scoreCandidate (unionProfiles P₁ P₂) scoreFun c =
          scoreCandidate P₁ scoreFun c + scoreCandidate P₂ scoreFun c := by
            simpa using
              (scoreCandidate_unionProfiles (P₁ := P₁) (P₂ := P₂) (score := scoreFun) (c := c))
      _ ≤ max₁ + max₂ := by
            exact add_le_add (hle1 c) (hle2 c)
  let scoreSet : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate (unionProfiles P₁ P₂) scoreFun c))
  let maxScore : Int :=
    scoreSet.max' (by
      simpa [scoreSet, Finset.Nonempty] using hA)
  have hmax_le : maxScore ≤ max₁ + max₂ := by
    have hscoreSet_nonempty : scoreSet.Nonempty := by
      simpa [scoreSet, Finset.Nonempty] using hA
    refine (Finset.max'_le_iff scoreSet hscoreSet_nonempty).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨c, _hc, rfl⟩
    exact hle_union c
  have hle_max : max₁ + max₂ ≤ maxScore := by
    have hmem :
        scoreCandidate (unionProfiles P₁ P₂) scoreFun x ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
    have hle : scoreCandidate (unionProfiles P₁ P₂) scoreFun x ≤ maxScore :=
      Finset.le_max' scoreSet _ hmem
    simpa [hsum_x] using hle
  have hmax_eq : maxScore = max₁ + max₂ :=
    le_antisymm hmax_le hle_max
  apply Finset.ext
  intro y
  constructor
  · intro hy
    have hy' : y ∈ scoringWinners (unionProfiles P₁ P₂) scoreFun := by
      simpa [scoringRule, scoreFun] using hy
    have hy_score :
        scoreCandidate (unionProfiles P₁ P₂) scoreFun y = maxScore := by
      simpa [scoringWinners, hA, scoreSet, maxScore] using hy'
    have hy_sum :
        scoreCandidate P₁ scoreFun y + scoreCandidate P₂ scoreFun y = max₁ + max₂ := by
      have hy_union :
          scoreCandidate (unionProfiles P₁ P₂) scoreFun y =
            scoreCandidate P₁ scoreFun y + scoreCandidate P₂ scoreFun y := by
        simpa using
          (scoreCandidate_unionProfiles (P₁ := P₁) (P₂ := P₂) (score := scoreFun) (c := y))
      simpa [hy_union, hmax_eq] using hy_score
    have hle1y : scoreCandidate P₁ scoreFun y ≤ max₁ := hle1 y
    have hle2y : scoreCandidate P₂ scoreFun y ≤ max₂ := hle2 y
    have hy1 : scoreCandidate P₁ scoreFun y = max₁ := by
      linarith
    have hy2 : scoreCandidate P₂ scoreFun y = max₂ := by
      linarith
    have hy1' : y ∈ scoringWinners P₁ scoreFun := by
      have hy_mem : y ∈ (Finset.univ : Finset A) := by simp
      have : y ∈ (Finset.univ.filter
          (fun c => scoreCandidate P₁ scoreFun c = max₁)) := by
        exact Finset.mem_filter.mpr ⟨hy_mem, hy1⟩
      simpa [scoringWinners, hA, scoreSet₁, max₁] using this
    have hy2' : y ∈ scoringWinners P₂ scoreFun := by
      have hy_mem : y ∈ (Finset.univ : Finset A) := by simp
      have : y ∈ (Finset.univ.filter
          (fun c => scoreCandidate P₂ scoreFun c = max₂)) := by
        exact Finset.mem_filter.mpr ⟨hy_mem, hy2⟩
      simpa [scoringWinners, hA, scoreSet₂, max₂] using this
    exact Finset.mem_inter.mpr
      ⟨by simpa [scoringRule, scoreFun] using hy1',
       by simpa [scoringRule, scoreFun] using hy2'⟩
  · intro hy
    have hy1 : y ∈ scoringWinners P₁ scoreFun := by
      simpa [scoringRule, scoreFun] using (Finset.mem_inter.mp hy).1
    have hy2 : y ∈ scoringWinners P₂ scoreFun := by
      simpa [scoringRule, scoreFun] using (Finset.mem_inter.mp hy).2
    have hy1' : scoreCandidate P₁ scoreFun y = max₁ := by
      simpa [scoringWinners, hA, scoreSet₁, max₁] using hy1
    have hy2' : scoreCandidate P₂ scoreFun y = max₂ := by
      simpa [scoringWinners, hA, scoreSet₂, max₂] using hy2
    have hy_union :
        scoreCandidate (unionProfiles P₁ P₂) scoreFun y = maxScore := by
      calc
        scoreCandidate (unionProfiles P₁ P₂) scoreFun y =
            scoreCandidate P₁ scoreFun y + scoreCandidate P₂ scoreFun y := by
              simpa using
                (scoreCandidate_unionProfiles
                  (P₁ := P₁) (P₂ := P₂) (score := scoreFun) (c := y))
        _ = max₁ + max₂ := by simpa [hy1', hy2']
        _ = maxScore := by simpa [hmax_eq] using (rfl : max₁ + max₂ = max₁ + max₂)
    have hy_mem : y ∈ (Finset.univ : Finset A) := by simp
    have : y ∈ (Finset.univ.filter
        (fun c => scoreCandidate (unionProfiles P₁ P₂) scoreFun c = maxScore)) := by
      exact Finset.mem_filter.mpr ⟨hy_mem, hy_union⟩
    have hy' : y ∈ scoringWinners (unionProfiles P₁ P₂) scoreFun := by
      simpa [scoringWinners, hA, scoreSet, maxScore] using this
    simpa [scoringRule, scoreFun] using hy'

end SocialChoice
