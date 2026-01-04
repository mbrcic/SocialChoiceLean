import Mathlib.Data.Fintype.Card
import SocialChoice.Axioms.Neutrality
import SocialChoice.Rank
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

lemma rank_relabelBallot_symm {A : Type} [Fintype A] (r : LinearOrder A)
    (σ : Equiv.Perm A) (c : A) :
    rank (relabelBallot r σ.symm) (σ c) = rank r c := by
  classical
  have hlt :
      ∀ {a b : A}, (relabelBallot r σ.symm).lt a b ↔ r.lt (σ.symm a) (σ.symm b) := by
    intro a b
    rfl
  have hcard :
      (Finset.univ.filter (fun d => r.lt (σ.symm d) c)).card =
        (Finset.univ.filter (fun d => r.lt d c)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun d => r.lt (σ.symm d) c))
      (t := Finset.univ.filter (fun d => r.lt d c))
      (i := fun a _ => σ.symm a) ?_ ?_ ?_
    · intro a ha
      have ha' : r.lt (σ.symm a) c := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨by simp, ha'⟩
    · intro a1 ha1 a2 ha2 h
      exact σ.symm.injective h
    · intro b hb
      refine ⟨σ b, ?_, by simp⟩
      have hb' : r.lt b c := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hb'⟩
  simpa [rank, hlt] using hcard

-- Any scoring rule is neutral.
theorem scoringRule_neutral (score : Nat → Nat → Int) : Neutrality (scoringRule score) := by
  intro V A _ _ P σ
  classical
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
  have score_perm :
      ∀ c, scoreCandidate (permuteCandidates P σ) scoreFun (σ c) =
        scoreCandidate P scoreFun c := by
    intro c
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hrank :
        rank (relabelBallot (P.pref v) σ.symm) (σ c) = rank (P.pref v) c := by
      simpa using (rank_relabelBallot_symm (r := P.pref v) (σ := σ) (c := c))
    simp [permuteCandidates, scoreFun, hrank]
  have score_perm' :
      ∀ c, scoreCandidate (permuteCandidates P σ) scoreFun c =
        scoreCandidate P scoreFun (σ.symm c) := by
    intro c
    have h := score_perm (σ.symm c)
    simpa using h
  by_cases h : (Finset.univ : Finset A).Nonempty
  ·
    have winner_iff :
        ∀ {P' : Profile V A} {c : A},
          c ∈ scoringWinners P' scoreFun ↔
            ∀ d : A, scoreCandidate P' scoreFun d ≤ scoreCandidate P' scoreFun c := by
      intro P' c
      let scoreSet : Finset Int :=
        (Finset.univ.image (fun c => scoreCandidate P' scoreFun c))
      let maxScore : Int :=
        scoreSet.max' (by
          simpa [scoreSet, Finset.Nonempty] using h)
      constructor
      · intro hc
        have hc' : scoreCandidate P' scoreFun c = maxScore := by
          simpa [scoringWinners, h, scoreSet, maxScore] using hc
        intro d
        have hmem : scoreCandidate P' scoreFun d ∈ scoreSet := by
          exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
        have hle : scoreCandidate P' scoreFun d ≤ maxScore :=
          Finset.le_max' scoreSet _ hmem
        simpa [hc'] using hle
      · intro hmax
        have hmem : scoreCandidate P' scoreFun c ∈ scoreSet := by
          exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
        have hle : scoreCandidate P' scoreFun c ≤ maxScore :=
          Finset.le_max' scoreSet _ hmem
        have hscoreSet_nonempty : scoreSet.Nonempty := by
          simpa [scoreSet, Finset.Nonempty] using h
        have hge : maxScore ≤ scoreCandidate P' scoreFun c := by
          refine (Finset.max'_le_iff scoreSet hscoreSet_nonempty).2 ?_
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨d, _hd, rfl⟩
          exact hmax d
        have hEq : scoreCandidate P' scoreFun c = maxScore :=
          le_antisymm hle hge
        have hc' :
            c ∈ (Finset.univ.filter
              (fun c => scoreCandidate P' scoreFun c = maxScore)) := by
          exact Finset.mem_filter.mpr ⟨by simp, hEq⟩
        simpa [scoringWinners, h, scoreSet, maxScore] using hc'
    apply Finset.ext
    intro c
    constructor
    · intro hc
      have hc0 : σ.symm c ∈ scoringRule score P := by
        simpa [permuteWinners] using hc
      have hmax0 :
          ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun (σ.symm c) :=
        (winner_iff.mp (by simpa [scoringRule, scoreFun] using hc0))
      have hmax_new :
          ∀ d, scoreCandidate (permuteCandidates P σ) scoreFun d ≤
            scoreCandidate (permuteCandidates P σ) scoreFun c := by
        intro d
        have hmax0' := hmax0 (σ.symm d)
        have hleft : scoreCandidate (permuteCandidates P σ) scoreFun d =
            scoreCandidate P scoreFun (σ.symm d) := score_perm' d
        have hright : scoreCandidate (permuteCandidates P σ) scoreFun c =
            scoreCandidate P scoreFun (σ.symm c) := score_perm' c
        simpa [hleft, hright] using hmax0'
      have hwin_new :
          c ∈ scoringWinners (permuteCandidates P σ) scoreFun :=
        (winner_iff.mpr hmax_new)
      simpa [scoringRule, scoreFun] using hwin_new
    · intro hc
      have hmax_new :
          ∀ d, scoreCandidate (permuteCandidates P σ) scoreFun d ≤
            scoreCandidate (permuteCandidates P σ) scoreFun c :=
        (winner_iff.mp (by simpa [scoringRule, scoreFun] using hc))
      have hmax_old :
          ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun (σ.symm c) := by
        intro d
        have hmax_new' := hmax_new (σ d)
        have hleft : scoreCandidate (permuteCandidates P σ) scoreFun (σ d) =
            scoreCandidate P scoreFun d := score_perm d
        have hright : scoreCandidate (permuteCandidates P σ) scoreFun c =
            scoreCandidate P scoreFun (σ.symm c) := score_perm' c
        simpa [hleft, hright] using hmax_new'
      have hwin_old :
          σ.symm c ∈ scoringWinners P scoreFun :=
        (winner_iff.mpr hmax_old)
      have hmap : c ∈ permuteWinners σ (scoringWinners P scoreFun) := by
        simpa [permuteWinners] using hwin_old
      simpa [scoringRule, scoreFun] using hmap
  · simp [scoringRule, scoringWinners, h, permuteWinners]

end SocialChoice
