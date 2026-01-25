import SocialChoice.Impossibilities.Holliday.Basic

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

-- Ballots from the updated profile and Key Figure in holliday_impossibility_small.tex.
def ballot_daceb : ListBallot 5 := ListBallot.mk' [d, a, c, e, b]
def ballot_ebacd : ListBallot 5 := ListBallot.mk' [e, b, a, c, d]
def ballot_bcaed : ListBallot 5 := ListBallot.mk' [b, c, a, e, d]
def ballot_cdeba : ListBallot 5 := ListBallot.mk' [c, d, e, b, a]
def ballot_dbace : ListBallot 5 := ListBallot.mk' [d, b, a, c, e]
def ballot_bacde : ListBallot 5 := ListBallot.mk' [b, a, c, d, e]
def ballot_adbec : ListBallot 5 := ListBallot.mk' [a, d, b, e, c]
def ballot_bdeac : ListBallot 5 := ListBallot.mk' [b, d, e, a, c]
def ballot_edcba : ListBallot 5 := ListBallot.mk' [e, d, c, b, a]

end Holliday

end SocialChoice
