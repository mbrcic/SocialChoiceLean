import SocialChoice.Rules
import SocialChoice.Meta

namespace SocialChoice

def vetoScore (m r : Nat) : Int := if r = m - 1 then 0 else 1

@[scRule]
noncomputable def veto : VotingRule :=
  scoringRule vetoScore

end SocialChoice
