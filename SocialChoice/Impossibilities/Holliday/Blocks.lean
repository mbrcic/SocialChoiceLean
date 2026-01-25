import SocialChoice.Impossibilities.Holliday.Ballots

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

/-! Block lists for margins (counts match the updated profile and Key Figure). -/

def blocksP1 : List (Nat × ListBallot 5) :=
  [(69, ballot_daceb), (64, ballot_ebacd), (46, ballot_bcaed), (20, ballot_cdeba),
   (18, ballot_dbace), (2, ballot_edcba)]

def blocksP2 : List (Nat × ListBallot 5) :=
  blocksP1 ++ [(26, ballot_adbec)]

def blocksP3 : List (Nat × ListBallot 5) :=
  [(62, ballot_daceb), (64, ballot_ebacd), (46, ballot_bcaed), (20, ballot_cdeba),
   (18, ballot_dbace), (2, ballot_edcba), (26, ballot_adbec)]

def blocksP4 : List (Nat × ListBallot 5) :=
  blocksP3 ++ [(23, ballot_bdeac)]

def blocksP5 : List (Nat × ListBallot 5) :=
  [(62, ballot_daceb), (64, ballot_ebacd), (46, ballot_bcaed), (20, ballot_cdeba),
   (11, ballot_dbace), (2, ballot_edcba), (26, ballot_adbec), (23, ballot_bdeac)]

end Holliday

end SocialChoice
