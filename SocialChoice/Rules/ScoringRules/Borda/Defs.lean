import SocialChoice.Rules

namespace SocialChoice

def bordaScore (m r : Nat) : Int := Int.ofNat (m - 1 - r)

noncomputable def borda : VotingRule :=
  scoringRule bordaScore

end SocialChoice
