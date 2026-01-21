import SocialChoice.Impossibilities.Holliday.Basic

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

-- Ballots from the updated profile and Key Figure in holliday_impossibility.tex.
def ballot_daceb : ListBallot 5 := ListBallot.mk' [d, a, c, e, b]
def ballot_ebacd : ListBallot 5 := ListBallot.mk' [e, b, a, c, d]
def ballot_bcaed : ListBallot 5 := ListBallot.mk' [b, c, a, e, d]
def ballot_cedba : ListBallot 5 := ListBallot.mk' [c, e, d, b, a]
def ballot_dbcae : ListBallot 5 := ListBallot.mk' [d, b, c, a, e]
def ballot_bacde : ListBallot 5 := ListBallot.mk' [b, a, c, d, e]
def ballot_adbec : ListBallot 5 := ListBallot.mk' [a, d, b, e, c]
def ballot_bdeac : ListBallot 5 := ListBallot.mk' [b, d, e, a, c]

end Holliday

end SocialChoice
