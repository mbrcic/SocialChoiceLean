import SocialChoice.Rules
import SocialChoice.Meta

namespace SocialChoice

def vetoScore (m r : Nat) : Int := if r = m - 1 then 0 else 1

@[scRule]
noncomputable def veto : VotingRule :=
  scoringRule vetoScore

theorem veto_isVotingRule : IsVotingRule veto := by
  intro V A _ _ _ P
  classical
  simpa [veto] using
    (scoringRule_isVotingRule (score := vetoScore) (V := V) (A := A) (P := P))

end SocialChoice
