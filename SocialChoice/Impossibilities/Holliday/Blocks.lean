import SocialChoice.Impossibilities.Holliday.Ballots

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

/-! Block lists for margins (counts match the updated profile and Key Figure). -/

def blocksP1 : List (Nat × ListBallot 5) :=
  [(69, ballot_daceb), (67, ballot_ebacd), (27, ballot_bcaed), (21, ballot_cedba),
   (20, ballot_dbcae), (18, ballot_bacde)]

def blocksP2 : List (Nat × ListBallot 5) :=
  blocksP1 ++ [(27, ballot_adbec)]

def blocksP3 : List (Nat × ListBallot 5) :=
  [(63, ballot_daceb), (67, ballot_ebacd), (27, ballot_bcaed), (21, ballot_cedba),
   (20, ballot_dbcae), (18, ballot_bacde), (27, ballot_adbec)]

def blocksP4 : List (Nat × ListBallot 5) :=
  blocksP3 ++ [(24, ballot_bdeac)]

def blocksP5 : List (Nat × ListBallot 5) :=
  [(63, ballot_daceb), (67, ballot_ebacd), (27, ballot_bcaed), (21, ballot_cedba),
   (13, ballot_dbcae), (18, ballot_bacde), (27, ballot_adbec), (24, ballot_bdeac)]

end Holliday

end SocialChoice
