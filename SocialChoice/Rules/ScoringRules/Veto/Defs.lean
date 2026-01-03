import SocialChoice.Rules

namespace SocialChoice

def vetoScore (m r : Nat) : Int := if r = m - 1 then 0 else 1

noncomputable def veto : VotingRule :=
  scoringRule vetoScore

end SocialChoice
