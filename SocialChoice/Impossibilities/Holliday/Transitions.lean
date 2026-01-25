import SocialChoice.Impossibilities.Holliday.Profiles
import SocialChoice.Axioms.Participation

namespace SocialChoice

open Finset

namespace Holliday

private lemma idxOf_head_lt_idxOf_of_ne {x c : A5} {rest : List A5} (hx : x ≠ c) :
    List.idxOf c (c :: rest) < List.idxOf x (c :: rest) := by
  have hx' : c ≠ x := Ne.symm hx
  simp [List.idxOf_cons_ne, hx']

lemma ballot_adbec_top_a : BallotTop ballot_adbec.toLinearOrder a := by
  intro x hx
  have hidx : ballot_adbec.ranking.idxOf a < ballot_adbec.ranking.idxOf x := by
    change List.idxOf a [a, d, b, e, c] < List.idxOf x [a, d, b, e, c]
    simpa using (idxOf_head_lt_idxOf_of_ne (x := x) (c := a) (rest := [d, b, e, c]) hx)
  exact (ListBallot.lt_iff_idxOf (b := ballot_adbec) (a := a) (c := x)).2 hidx

lemma ballot_daceb_top_d : BallotTop ballot_daceb.toLinearOrder d := by
  intro x hx
  have hidx : ballot_daceb.ranking.idxOf d < ballot_daceb.ranking.idxOf x := by
    change List.idxOf d [d, a, c, e, b] < List.idxOf x [d, a, c, e, b]
    simpa using (idxOf_head_lt_idxOf_of_ne (x := x) (c := d) (rest := [a, c, e, b]) hx)
  exact (ListBallot.lt_iff_idxOf (b := ballot_daceb) (a := d) (c := x)).2 hidx

lemma ballot_bdeac_top_b : BallotTop ballot_bdeac.toLinearOrder b := by
  intro x hx
  have hidx : ballot_bdeac.ranking.idxOf b < ballot_bdeac.ranking.idxOf x := by
    change List.idxOf b [b, d, e, a, c] < List.idxOf x [b, d, e, a, c]
    simpa using (idxOf_head_lt_idxOf_of_ne (x := x) (c := b) (rest := [d, e, a, c]) hx)
  exact (ListBallot.lt_iff_idxOf (b := ballot_bdeac) (a := b) (c := x)).2 hidx

lemma ballot_dbace_top_d : BallotTop ballot_dbace.toLinearOrder d := by
  intro x hx
  have hidx : ballot_dbace.ranking.idxOf d < ballot_dbace.ranking.idxOf x := by
    change List.idxOf d [d, b, a, c, e] < List.idxOf x [d, b, a, c, e]
    simpa using (idxOf_head_lt_idxOf_of_ne (x := x) (c := d) (rest := [b, a, c, e]) hx)
  exact (ListBallot.lt_iff_idxOf (b := ballot_dbace) (a := d) (c := x)).2 hidx

lemma not_mem_addCopiesProfile_of_not_mem {f : VotingRule} (hpos : PositiveInvolvement f)
    {U A : Type} [DecidableEq U] [Fintype A]
    (V W : Finset U) (hVW : Disjoint V W)
    (P : Profile (Electorate U V) A) (r : LinearOrder A) (c : A)
    (htop : BallotTop r c) :
    c ∉ f (addCopiesProfile V W P r) → c ∉ f P := by
  intro hnot hc
  have hmem :
      c ∈ f (addCopiesProfile V W P r) :=
    positiveInvolvement_addCopiesProfile (f := f) hpos V W hVW P r c htop hc
  exact hnot hmem

lemma mem_P2_of_mem_P1 {f : VotingRule} (hpos : PositiveInvolvement f)
    (ha : a ∈ f P1Profile) : a ∈ f P2Profile := by
  have hmem :
      a ∈ f (addCopiesProfile votersP1 votersP1_9 P1Profile ballot_adbec.toLinearOrder) :=
    positiveInvolvement_addCopiesProfile (f := f) hpos votersP1 votersP1_9
      votersP1_disjoint_votersP1_9 P1Profile ballot_adbec.toLinearOrder a
      ballot_adbec_top_a ha
  have hmem' :
      a ∈ f (castProfile (h := votersP2_eq_union_votersP1_votersP1_9)
        (addCopiesProfile votersP1 votersP1_9 P1Profile ballot_adbec.toLinearOrder)) := by
    have hcast :=
      votingRule_castProfile (f := f) (h := votersP2_eq_union_votersP1_votersP1_9)
        (P := addCopiesProfile votersP1 votersP1_9 P1Profile ballot_adbec.toLinearOrder)
    rw [hcast]
    exact hmem
  have hmem'' : a ∈ f P2Profile := by
    rw [P2Profile_eq_addCopiesProfile_P1]
    exact hmem'
  exact hmem''

lemma not_mem_P3_of_not_mem_P2 {f : VotingRule} (hpos : PositiveInvolvement f)
    (hd : d ∉ f P2Profile) : d ∉ f P3Profile := by
  intro hd3
  have hmem :
      d ∈ f (addCopiesProfile votersP3 votersP1_2 P3Profile ballot_daceb.toLinearOrder) :=
    positiveInvolvement_addCopiesProfile (f := f) hpos votersP3 votersP1_2
      votersP3_disjoint_votersP1_2 P3Profile ballot_daceb.toLinearOrder d
      ballot_daceb_top_d hd3
  have hmem' :
      d ∈ f (castProfile (h := votersP2_eq_union_votersP3_votersP1_2)
        (addCopiesProfile votersP3 votersP1_2 P3Profile ballot_daceb.toLinearOrder)) := by
    have hcast :=
      votingRule_castProfile (f := f) (h := votersP2_eq_union_votersP3_votersP1_2)
        (P := addCopiesProfile votersP3 votersP1_2 P3Profile ballot_daceb.toLinearOrder)
    rw [hcast]
    exact hmem
  have hmem'' : d ∈ f P2Profile := by
    rw [P2Profile_eq_addCopiesProfile_P3]
    exact hmem'
  exact hd hmem''

lemma mem_P4_of_mem_P3 {f : VotingRule} (hpos : PositiveInvolvement f)
    (hb : b ∈ f P3Profile) : b ∈ f P4Profile := by
  have hmem :
      b ∈ f (addCopiesProfile votersP3 votersP1_10 P3Profile ballot_bdeac.toLinearOrder) :=
    positiveInvolvement_addCopiesProfile (f := f) hpos votersP3 votersP1_10
      votersP3_disjoint_votersP1_10 P3Profile ballot_bdeac.toLinearOrder b
      ballot_bdeac_top_b hb
  have hmem' :
      b ∈ f (castProfile (h := votersP4_eq_union_votersP3_votersP1_10)
        (addCopiesProfile votersP3 votersP1_10 P3Profile ballot_bdeac.toLinearOrder)) := by
    have hcast :=
      votingRule_castProfile (f := f) (h := votersP4_eq_union_votersP3_votersP1_10)
        (P := addCopiesProfile votersP3 votersP1_10 P3Profile ballot_bdeac.toLinearOrder)
    rw [hcast]
    exact hmem
  have hmem'' : b ∈ f P4Profile := by
    rw [P4Profile_eq_addCopiesProfile_P3]
    exact hmem'
  exact hmem''

lemma not_mem_P5_of_not_mem_P4 {f : VotingRule} (hpos : PositiveInvolvement f)
    (hd : d ∉ f P4Profile) : d ∉ f P5Profile := by
  intro hd5
  have hmem :
      d ∈ f (addCopiesProfile votersP5 votersP1_7 P5Profile ballot_dbace.toLinearOrder) :=
    positiveInvolvement_addCopiesProfile (f := f) hpos votersP5 votersP1_7
      votersP5_disjoint_votersP1_7 P5Profile ballot_dbace.toLinearOrder d
      ballot_dbace_top_d hd5
  have hmem' :
      d ∈ f (castProfile (h := votersP4_eq_union_votersP5_votersP1_7)
        (addCopiesProfile votersP5 votersP1_7 P5Profile ballot_dbace.toLinearOrder)) := by
    have hcast :=
      votingRule_castProfile (f := f) (h := votersP4_eq_union_votersP5_votersP1_7)
        (P := addCopiesProfile votersP5 votersP1_7 P5Profile ballot_dbace.toLinearOrder)
    rw [hcast]
    exact hmem
  have hmem'' : d ∈ f P4Profile := by
    rw [P4Profile_eq_addCopiesProfile_P5]
    exact hmem'
  exact hd hmem''

end Holliday

end SocialChoice
