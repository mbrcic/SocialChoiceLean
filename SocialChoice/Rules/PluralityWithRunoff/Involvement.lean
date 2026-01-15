import Mathlib.Tactic
import SocialChoice.Axioms.Participation
import SocialChoice.Margin
import SocialChoice.Rules.PluralityWithRunoff.Defs
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser

namespace SocialChoice

open Finset

private lemma max_of_mem_plurality {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c : A} (hc : c ∈ plurality P) :
    ∀ d : A, topCount P d ≤ topCount P c := by
  have hc' :
      c ∈ (Finset.univ.filter (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
    simpa [plurality] using hc
  exact (Finset.mem_filter.mp hc').2

private lemma max_of_mem_secondPluralitySet {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A) {y : A} (hy : y ∈ secondPluralitySet P S) :
    ∀ d : A, d ∉ S → topCount P d ≤ topCount P y := by
  classical
  let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
  by_cases hR : R.Nonempty
  · have hy' :
        y ∈ R.filter (fun c => topCount P c =
          (R.image (fun c => topCount P c)).max' (by
            simpa [Finset.Nonempty] using hR.image (fun c => topCount P c))) := by
      simpa [secondPluralitySet, hR, R] using hy
    have hyEq :
        topCount P y =
          (R.image (fun c => topCount P c)).max' (by
            simpa [Finset.Nonempty] using hR.image (fun c => topCount P c)) :=
      (Finset.mem_filter.mp hy').2
    intro d hdS
    have hdR : d ∈ R := Finset.mem_filter.mpr ⟨mem_univ d, hdS⟩
    have hmem : topCount P d ∈ R.image (fun c => topCount P c) :=
      Finset.mem_image.mpr ⟨d, hdR, rfl⟩
    have hle :
        topCount P d ≤
          (R.image (fun c => topCount P c)).max' (by
            simpa [Finset.Nonempty] using hR.image (fun c => topCount P c)) :=
      Finset.le_max' _ _ hmem
    simpa [hyEq] using hle
  · have hfalse : False := by
      simp [secondPluralitySet, R, hR] at hy
    exact hfalse.elim

private lemma mem_secondPluralitySet_of_max {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A) {y : A} (hyS : y ∉ S)
    (hmax : ∀ d : A, d ∉ S → topCount P d ≤ topCount P y) :
    y ∈ secondPluralitySet P S := by
  classical
  let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
  have hyR : y ∈ R := Finset.mem_filter.mpr ⟨mem_univ y, hyS⟩
  have hR : R.Nonempty := ⟨y, hyR⟩
  let scoreSet : Finset Nat := R.image (fun c => topCount P c)
  have hscoreSet_nonempty : scoreSet.Nonempty := hR.image (fun c => topCount P c)
  let maxScore : Nat := scoreSet.max' hscoreSet_nonempty
  have hy_le : topCount P y ≤ maxScore := by
    have hmem : topCount P y ∈ scoreSet := Finset.mem_image.mpr ⟨y, hyR, rfl⟩
    exact Finset.le_max' scoreSet _ hmem
  have hge : maxScore ≤ topCount P y := by
    refine (Finset.max'_le_iff scoreSet hscoreSet_nonempty).2 ?_
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨d, hd, rfl⟩
    have hdS : d ∉ S := (Finset.mem_filter.mp hd).2
    exact hmax d hdS
  have hEq : topCount P y = maxScore := le_antisymm hy_le hge
  have hyMem : y ∈ R.filter (fun c => topCount P c = maxScore) :=
    Finset.mem_filter.mpr ⟨hyR, hEq⟩
  simpa [secondPluralitySet, hR, R, scoreSet, maxScore] using hyMem

theorem pluralityWithRunoff_positiveInvolvement : PositiveInvolvement pluralityWithRunoff := by
  intro V A _ _ P x ballot hx htop
  classical
  letI : DecidableEq A := Classical.decEq A
  by_cases hcard : Fintype.card A ≤ 1
  · simp [pluralityWithRunoff, hcard]
  · let P' := addVoter P ballot
    obtain ⟨y, hpair, hmargin⟩ := by
      simpa [pluralityWithRunoff, hcard] using hx
    have hpair_card : ({x, y} : Finset A).card = 2 :=
      mem_pluralityWithRunoffPairs_card (P := P) hpair
    have hxy : x ≠ y := by
      by_contra hxy
      simp [hxy] at hpair_card
    have hyx : y ≠ x := by
      simpa [eq_comm] using hxy
    have hmargin' : 0 ≤ margin P' x y := by
      have hxylt : ballot.lt x y := htop y (by simpa [eq_comm] using hxy)
      have hmargin_eq : margin P' x y = margin P x y + 1 :=
        margin_addVoter_eq_of_prefers P ballot x y hxylt
      linarith
    have ballot_not_top : ∀ d : A, d ≠ x → ¬ BallotTop ballot d := by
      intro d hne htopd
      have hxd : ballot.lt x d := htop d hne
      have hdx : ballot.lt d x := htopd x (by simpa [eq_comm] using hne)
      let _ : Preorder A := ballot.toPreorder
      exact (lt_asymm (a := x) (b := d) hxd) hdx
    let rightTop : A → Finset Unit :=
      fun d => if BallotTop ballot d then {()} else ∅
    have votersTop_addVoter :
        ∀ d : A, votersTop P' d = (votersTop P d).disjSum (rightTop d) := by
      intro d
      ext v
      cases v with
      | inl v =>
          simp [votersTop, P', addVoter, TopRank, Prefers, rightTop,
            Finset.inl_mem_disjSum]
      | inr u =>
          cases u
          have hL : Sum.inr PUnit.unit ∈ votersTop P' d ↔ BallotTop ballot d := by
            simp [votersTop, P', addVoter, TopRank, Prefers, BallotTop]
          by_cases hbt : BallotTop ballot d
          · simp [hL, rightTop, hbt, Finset.inr_mem_disjSum]
          · simp [hL, rightTop, hbt]
    have topCount_addVoter :
        ∀ d : A, topCount P' d = topCount P d + (rightTop d).card := by
      intro d
      unfold topCount
      simp [votersTop_addVoter, Finset.card_disjSum]
    have topCount_x : topCount P' x = topCount P x + 1 := by
      have : rightTop x = {()} := by
        simp [rightTop, htop]
      simpa [this] using topCount_addVoter x
    have topCount_ne : ∀ d : A, d ≠ x → topCount P' d = topCount P d := by
      intro d hne
      have : rightTop d = ∅ := by
        simp [rightTop, ballot_not_top d hne]
      simpa [this] using topCount_addVoter d
    let S := plurality P
    let S' := plurality P'
    have hpair_new : ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P' := by
      by_cases hxS : x ∈ S
      · have hmax_x : ∀ d : A, topCount P d ≤ topCount P x :=
          max_of_mem_plurality (P := P) hxS
        have hxS' : x ∈ S' := by
          have hmax_x' : ∀ d : A, topCount P' d ≤ topCount P' x := by
            intro d
            by_cases hdx : d = x
            · simp [hdx]
            · calc
                topCount P' d = topCount P d := topCount_ne d hdx
                _ ≤ topCount P x := hmax_x d
                _ ≤ topCount P x + 1 := Nat.le_succ _
                _ = topCount P' x := topCount_x.symm
          have hx' :
              x ∈ (Finset.univ.filter (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) :=
            Finset.mem_filter.mpr ⟨mem_univ x, hmax_x'⟩
          simpa [plurality, S'] using hx'
        have hS'Eq : S' = {x} := by
          apply Finset.ext
          intro z
          constructor
          · intro hz
            by_contra hzx
            have hzx' : z ≠ x := by
              simpa using hzx
            have hz' :
                z ∈ (Finset.univ.filter (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) := by
              simpa [plurality, S'] using hz
            have hzmax : ∀ d : A, topCount P' d ≤ topCount P' z :=
              (Finset.mem_filter.mp hz').2
            have hlt : topCount P' z < topCount P' x := by
              calc
                topCount P' z = topCount P z := topCount_ne z hzx'
                _ < topCount P x + 1 := Nat.lt_succ_of_le (hmax_x z)
                _ = topCount P' x := topCount_x.symm
            have hle : topCount P' x ≤ topCount P' z := hzmax x
            exact (not_lt_of_ge hle) hlt
          · intro hz
            have hz' : z = x := by simpa using hz
            subst hz'
            exact hxS'
        have hS'card : ¬ S'.card ≥ 2 := by
          simp [hS'Eq]
        have hyMax : ∀ d : A, d ≠ x → topCount P d ≤ topCount P y := by
          by_cases hS : S.card ≥ 2
          · have hpairS : ({x, y} : Finset A) ∈ S.powersetCard 2 := by
              simpa [pluralityWithRunoffPairs, hS, S] using hpair
            have hsubset : ({x, y} : Finset A) ⊆ S :=
              (Finset.mem_powersetCard.mp hpairS).1
            have hyS : y ∈ S := hsubset (by simp)
            have hmax_y : ∀ d : A, topCount P d ≤ topCount P y :=
              max_of_mem_plurality (P := P) hyS
            intro d _hdx
            exact hmax_y d
          · have hpairS :
                ({x, y} : Finset A) ∈
                  (S.product (secondPluralitySet P S)).image
                    (fun p => ({p.1, p.2} : Finset A)) := by
              simpa [pluralityWithRunoffPairs, hS, S] using hpair
            rcases Finset.mem_image.mp hpairS with ⟨p, hp, hpEq⟩
            rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
            have hxS' : x ∈ S := by
              simpa using hxS
            have hx1 : x = p.1 := by
              have hxMem : x ∈ ({p.1, p.2} : Finset A) := by
                simp [hpEq]
              have hx' : x = p.1 ∨ x = p.2 := by
                simpa [Finset.mem_insert, Finset.mem_singleton] using hxMem
              cases hx' with
              | inl hx1 => exact hx1
              | inr hx2 =>
                  have : x ∈ secondPluralitySet P S := by simpa [hx2] using hp2
                  have hxnot : x ∉ S :=
                    mem_secondPluralitySet_not_mem (P := P) (S := S) this
                  exact (hxnot hxS').elim
            have hy2 : y = p.2 := by
              have hyMem : y ∈ ({p.1, p.2} : Finset A) := by
                simp [hpEq]
              have hy' : y = p.1 ∨ y = p.2 := by
                simpa [Finset.mem_insert, Finset.mem_singleton] using hyMem
              cases hy' with
              | inl hy1 =>
                  have : y = x := by simpa [hx1] using hy1
                  exact (hyx this).elim
              | inr hy2 => exact hy2
            have hySecond_old : y ∈ secondPluralitySet P S := by
              simpa [hy2] using hp2
            have hmax_y :
                ∀ d : A, d ∉ S → topCount P d ≤ topCount P y :=
              max_of_mem_secondPluralitySet (P := P) (S := S) hySecond_old
            intro d hdx
            have hScard : S.card = 1 := by
              have hSle : S.card ≤ 1 := by
                have hlt : S.card < 2 := lt_of_not_ge hS
                exact Nat.lt_succ_iff.mp hlt
              have hSge : 1 ≤ S.card := Finset.one_le_card.mpr ⟨x, hxS'⟩
              exact Nat.le_antisymm hSle hSge
            rcases Finset.card_eq_one.mp hScard with ⟨a, ha⟩
            have hx' : x = a := by
              have : x ∈ ({a} : Finset A) := by simpa [ha] using hxS'
              simpa [Finset.mem_singleton] using this
            have hSEq : S = {x} := by
              simp [ha, hx']
            have hdS : d ∉ S := by
              simpa [hSEq] using hdx
            exact hmax_y d hdS
        have hyS' : y ∉ S' := by
          simpa [hS'Eq] using hyx
        have hmax_y' : ∀ d : A, d ∉ S' → topCount P' d ≤ topCount P' y := by
          intro d hdS'
          have hdx : d ≠ x := by
            intro hdx
            subst hdx
            exact hdS' hxS'
          calc
            topCount P' d = topCount P d := topCount_ne d hdx
            _ ≤ topCount P y := hyMax d hdx
            _ = topCount P' y := (topCount_ne y hyx).symm
        have hySecond : y ∈ secondPluralitySet P' S' :=
          mem_secondPluralitySet_of_max (P := P') (S := S') hyS' hmax_y'
        have hpair' :
            ({x, y} : Finset A) ∈
              (S'.product (secondPluralitySet P' S')).image
                (fun p => ({p.1, p.2} : Finset A)) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨(x, y), ?_, rfl⟩
          exact Finset.mem_product.mpr ⟨hxS', hySecond⟩
        simpa [pluralityWithRunoffPairs, hS'card, S'] using hpair'
      · have hS : ¬ S.card ≥ 2 := by
          intro hS
          have hpairS : ({x, y} : Finset A) ∈ S.powersetCard 2 := by
            simpa [pluralityWithRunoffPairs, hS, S] using hpair
          have hsubset : ({x, y} : Finset A) ⊆ S :=
            (Finset.mem_powersetCard.mp hpairS).1
          have : x ∈ S := hsubset (by simp)
          exact (hxS this).elim
        have hpairS :
            ({x, y} : Finset A) ∈
              (S.product (secondPluralitySet P S)).image
                (fun p => ({p.1, p.2} : Finset A)) := by
          simpa [pluralityWithRunoffPairs, hS, S] using hpair
        rcases Finset.mem_image.mp hpairS with ⟨p, hp, hpEq⟩
        rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
        have hx2 : x = p.2 := by
          have hxMem : x ∈ ({p.1, p.2} : Finset A) := by
            simp [hpEq]
          have hx' : x = p.1 ∨ x = p.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hxMem
          cases hx' with
          | inl hx1 =>
              have : x ∈ S := by simpa [hx1] using hp1
              exact (hxS this).elim
          | inr hx2 => exact hx2
        have hy1 : y = p.1 := by
          have hyMem : y ∈ ({p.1, p.2} : Finset A) := by
            simp [hpEq]
          have hy' : y = p.1 ∨ y = p.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hyMem
          cases hy' with
          | inl hy1 => exact hy1
          | inr hy2 =>
              have : y = x := by simpa [hx2] using hy2
              exact (hyx this).elim
        have hxSecond_old : x ∈ secondPluralitySet P S := by
          simpa [hx2] using hp2
        have hyS : y ∈ S := by
          simpa [hy1] using hp1
        have hmax_x_old : ∀ d : A, d ∉ S → topCount P d ≤ topCount P x :=
          max_of_mem_secondPluralitySet (P := P) (S := S) hxSecond_old
        have hmax_y_old : ∀ d : A, topCount P d ≤ topCount P y :=
          max_of_mem_plurality (P := P) hyS
        have hScard : S.card = 1 := by
          have hSle : S.card ≤ 1 := by
            have hlt : S.card < 2 := lt_of_not_ge hS
            exact Nat.lt_succ_iff.mp hlt
          have hSge : 1 ≤ S.card := Finset.one_le_card.mpr ⟨y, hyS⟩
          exact Nat.le_antisymm hSle hSge
        have hSEq : S = {y} := by
          rcases Finset.card_eq_one.mp hScard with ⟨a, ha⟩
          have hy' : y = a := by
            have : y ∈ ({a} : Finset A) := by simpa [ha] using hyS
            simpa [Finset.mem_singleton] using this
          simp [ha, hy']
        have hcomp := lt_trichotomy (topCount P' x) (topCount P' y)
        cases hcomp with
        | inl hlt =>
            have hyS' : y ∈ S' := by
              have hmax_y' : ∀ d : A, topCount P' d ≤ topCount P' y := by
                intro d
                by_cases hdy : d = y
                · simp [hdy]
                · by_cases hdx : d = x
                  · simpa [hdx] using (le_of_lt hlt)
                  · calc
                      topCount P' d = topCount P d := topCount_ne d hdx
                      _ ≤ topCount P y := hmax_y_old d
                      _ = topCount P' y := (topCount_ne y hyx).symm
              have hy' :
                  y ∈ (Finset.univ.filter (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) :=
                Finset.mem_filter.mpr ⟨mem_univ y, hmax_y'⟩
              simpa [plurality, S'] using hy'
            have hS'Eq : S' = {y} := by
              apply Finset.ext
              intro z
              constructor
              · intro hz
                by_contra hzy
                have hz' :
                    z ∈ (Finset.univ.filter
                      (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) := by
                  simpa [plurality, S'] using hz
                have hzmax : ∀ d : A, topCount P' d ≤ topCount P' z :=
                  (Finset.mem_filter.mp hz').2
                have hle1 : topCount P' z ≤ topCount P' y := by
                  by_cases hzx : z = x
                  · simpa [hzx] using (le_of_lt hlt)
                  · calc
                      topCount P' z = topCount P z := topCount_ne z hzx
                      _ ≤ topCount P y := hmax_y_old z
                      _ = topCount P' y := (topCount_ne y hyx).symm
                have hle2 : topCount P' y ≤ topCount P' z := hzmax y
                have hEq : topCount P' z = topCount P' y := le_antisymm hle1 hle2
                by_cases hzx : z = x
                · have : topCount P' x = topCount P' y := by simpa [hzx] using hEq
                  exact (ne_of_lt hlt) this
                · have hEq' : topCount P z = topCount P y := by
                    calc
                      topCount P z = topCount P' z := (topCount_ne z hzx).symm
                      _ = topCount P' y := hEq
                      _ = topCount P y := topCount_ne y hyx
                  have hzmaxP : ∀ d : A, topCount P d ≤ topCount P z := by
                    intro d
                    have hle : topCount P d ≤ topCount P y := hmax_y_old d
                    simpa [hEq'] using hle
                  have hzS : z ∈ S := by
                    have hz' :
                        z ∈ (Finset.univ.filter
                          (fun c => ∀ d : A, topCount P d ≤ topCount P c)) :=
                      Finset.mem_filter.mpr ⟨mem_univ z, hzmaxP⟩
                    simpa [plurality, S] using hz'
                  have : z ∈ ({y} : Finset A) := by
                    simpa [hSEq] using hzS
                  exact hzy this
              · intro hz
                have hz' : z = y := by simpa using hz
                subst hz'
                exact hyS'
            have hS'card : ¬ S'.card ≥ 2 := by
              simp [hS'Eq]
            have hxS' : x ∉ S' := by
              simpa [hS'Eq] using hxy
            have hmax_x' : ∀ d : A, d ∉ S' → topCount P' d ≤ topCount P' x := by
              intro d hdS'
              have hdy : d ≠ y := by
                intro hdy
                subst hdy
                exact hdS' hyS'
              by_cases hdx : d = x
              · simp [hdx]
              · have hdS : d ∉ S := by
                  simpa [hSEq] using hdy
                calc
                  topCount P' d = topCount P d := topCount_ne d hdx
                  _ ≤ topCount P x := hmax_x_old d hdS
                  _ ≤ topCount P x + 1 := Nat.le_succ _
                  _ = topCount P' x := topCount_x.symm
            have hxSecond : x ∈ secondPluralitySet P' S' :=
              mem_secondPluralitySet_of_max (P := P') (S := S') hxS' hmax_x'
            have hpair' :
                ({x, y} : Finset A) ∈
                  (S'.product (secondPluralitySet P' S')).image
                    (fun p => ({p.1, p.2} : Finset A)) := by
              refine Finset.mem_image.mpr ?_
              refine ⟨(y, x), ?_, by simp [Finset.pair_comm]⟩
              exact Finset.mem_product.mpr ⟨hyS', hxSecond⟩
            simpa [pluralityWithRunoffPairs, hS'card, S'] using hpair'
        | inr hcomp' =>
            cases hcomp' with
            | inl heq =>
                have hxS' : x ∈ S' := by
                  have hmax_x' : ∀ d : A, topCount P' d ≤ topCount P' x := by
                    intro d
                    by_cases hdx : d = x
                    · simp [hdx]
                    · calc
                        topCount P' d = topCount P d := topCount_ne d hdx
                        _ ≤ topCount P y := hmax_y_old d
                        _ = topCount P' y := (topCount_ne y hyx).symm
                        _ = topCount P' x := heq.symm
                  have hx' :
                      x ∈ (Finset.univ.filter
                        (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) :=
                    Finset.mem_filter.mpr ⟨mem_univ x, hmax_x'⟩
                  simpa [plurality, S'] using hx'
                have hyS' : y ∈ S' := by
                  have hmax_y' : ∀ d : A, topCount P' d ≤ topCount P' y := by
                    intro d
                    by_cases hdy : d = y
                    · simp [hdy]
                    · by_cases hdx : d = x
                      · simp [hdx, heq]
                      · calc
                          topCount P' d = topCount P d := topCount_ne d hdx
                          _ ≤ topCount P y := hmax_y_old d
                          _ = topCount P' y := (topCount_ne y hyx).symm
                  have hy' :
                      y ∈ (Finset.univ.filter
                        (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) :=
                    Finset.mem_filter.mpr ⟨mem_univ y, hmax_y'⟩
                  simpa [plurality, S'] using hy'
                have hsubset : ({x, y} : Finset A) ⊆ S' := by
                  intro z hz
                  simp [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl
                  · exact hxS'
                  · exact hyS'
                have hcard_le : ({x, y} : Finset A).card ≤ S'.card :=
                  Finset.card_le_card hsubset
                have hS'card : S'.card ≥ 2 := by
                  simpa [hpair_card] using hcard_le
                have hpair' : ({x, y} : Finset A) ∈ S'.powersetCard 2 := by
                  exact Finset.mem_powersetCard.mpr ⟨hsubset, hpair_card⟩
                simpa [pluralityWithRunoffPairs, hS'card, S'] using hpair'
            | inr hgt =>
                have hxS' : x ∈ S' := by
                  have hmax_x' : ∀ d : A, topCount P' d ≤ topCount P' x := by
                    intro d
                    by_cases hdx : d = x
                    · simp [hdx]
                    · calc
                        topCount P' d = topCount P d := topCount_ne d hdx
                        _ ≤ topCount P y := hmax_y_old d
                        _ = topCount P' y := (topCount_ne y hyx).symm
                        _ ≤ topCount P' x := le_of_lt hgt
                  have hx' :
                      x ∈ (Finset.univ.filter
                        (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) :=
                    Finset.mem_filter.mpr ⟨mem_univ x, hmax_x'⟩
                  simpa [plurality, S'] using hx'
                have hS'Eq : S' = {x} := by
                  apply Finset.ext
                  intro z
                  constructor
                  · intro hz
                    by_contra hzx
                    have hzx' : z ≠ x := by
                      simpa using hzx
                    have hz' :
                        z ∈ (Finset.univ.filter
                          (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) := by
                      simpa [plurality, S'] using hz
                    have hzmax : ∀ d : A, topCount P' d ≤ topCount P' z :=
                      (Finset.mem_filter.mp hz').2
                    have hlt' : topCount P' z < topCount P' x := by
                      by_cases hzy' : z = y
                      · simpa [hzy'] using hgt
                      · calc
                          topCount P' z = topCount P z := topCount_ne z hzx'
                          _ ≤ topCount P y := hmax_y_old z
                          _ = topCount P' y := (topCount_ne y hyx).symm
                          _ < topCount P' x := hgt
                    have hle : topCount P' x ≤ topCount P' z := hzmax x
                    exact (not_lt_of_ge hle) hlt'
                  · intro hz
                    have hz' : z = x := by simpa using hz
                    subst hz'
                    exact hxS'
                have hS'card : ¬ S'.card ≥ 2 := by
                  simp [hS'Eq]
                have hyS' : y ∉ S' := by
                  simpa [hS'Eq] using hyx
                have hmax_y' : ∀ d : A, d ∉ S' → topCount P' d ≤ topCount P' y := by
                  intro d hdS'
                  have hdx : d ≠ x := by
                    intro hdx
                    subst hdx
                    exact hdS' hxS'
                  calc
                    topCount P' d = topCount P d := topCount_ne d hdx
                    _ ≤ topCount P y := hmax_y_old d
                    _ = topCount P' y := (topCount_ne y hyx).symm
                have hySecond : y ∈ secondPluralitySet P' S' :=
                  mem_secondPluralitySet_of_max (P := P') (S := S') hyS' hmax_y'
                have hpair' :
                    ({x, y} : Finset A) ∈
                      (S'.product (secondPluralitySet P' S')).image
                        (fun p => ({p.1, p.2} : Finset A)) := by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨(x, y), ?_, rfl⟩
                  exact Finset.mem_product.mpr ⟨hxS', hySecond⟩
                simpa [pluralityWithRunoffPairs, hS'card, S'] using hpair'
    have hx' :
        ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P' ∧
          0 ≤ margin P' x y := by
      exact ⟨y, hpair_new, hmargin'⟩
    simpa [pluralityWithRunoff, hcard] using hx'

end SocialChoice
