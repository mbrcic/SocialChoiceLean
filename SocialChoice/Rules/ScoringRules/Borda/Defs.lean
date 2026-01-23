import SocialChoice.Rules
import SocialChoice.Meta

namespace SocialChoice

def bordaScore (m r : Nat) : Int := Int.ofNat (m - 1 - r)

@[scRule]
noncomputable def borda : VotingRule :=
  scoringRule bordaScore

theorem borda_isVotingRule : IsVotingRule borda := by
  intro V A _ _ _ P
  classical
  simpa [borda] using
    (scoringRule_isVotingRule (score := bordaScore) (V := V) (A := A) (P := P))

lemma bordaScore_strictlyDecreasing : strictlyDecreasingScore bordaScore := by
  intro m r s hrs hrm hsm
  cases m with
  | zero =>
      exact (Nat.not_lt_zero _ hrm).elim
  | succ m =>
      dsimp [bordaScore]
      have hsle : s ≤ m := Nat.lt_succ_iff.mp hsm
      have hrlt : r < m := lt_of_lt_of_le hrs hsle
      have hsub : m - s < m - r := Nat.sub_lt_sub_left hrlt hrs
      exact Int.ofNat_lt_ofNat_of_lt hsub

end SocialChoice
