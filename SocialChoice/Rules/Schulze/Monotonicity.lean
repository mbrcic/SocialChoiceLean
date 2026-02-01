import SocialChoice.Axioms.Monotonicity
import SocialChoice.Margin
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path

namespace SocialChoice

open Finset

lemma pathStrength_eq_of_no_x {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x : A) (hLift : simpleLift P' P x) :
    ∀ l, x ∉ l → pathStrength P l = pathStrength P' l := by
  intro l hx
  induction l with
  | nil =>
      simp [pathStrength]
  | cons a t ih =>
      cases t with
      | nil =>
          simp [pathStrength]
      | cons b t' =>
          have hnot : x ≠ a ∧ x ∉ b :: t' := by
            simpa [List.mem_cons] using hx
          have ha : a ≠ x := by
            exact ne_comm.mp hnot.1
          have hnot' : x ∉ b :: t' := hnot.2
          have hnot'' : x ≠ b ∧ x ∉ t' := by
            simpa [List.mem_cons] using hnot'
          have hb : b ≠ x := by
            exact ne_comm.mp hnot''.1
          have hmargin :
              margin P a b = margin P' a b := by
            exact margin_eq_of_simpleLift P P' x a b ha hb hLift
          cases t' with
          | nil =>
              simp [pathStrength_two, hmargin]
          | cons c t'' =>
              have htail :
                  pathStrength P (b :: c :: t'') =
                    pathStrength P' (b :: c :: t'') := by
                exact ih (by simpa using hnot')
              simp [pathStrength_cons_cons_cons, hmargin, htail]

lemma pathStrength_le_of_head_x {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x : A) (hLift : simpleLift P' P x) :
    ∀ l, l.head? = some x → l.Nodup → pathStrength P l ≤ pathStrength P' l := by
  intro l hhead hnodup
  cases l with
  | nil =>
      cases hhead
  | cons a t =>
      have ha : a = x := by
        simpa using hhead
      subst a
      cases t with
      | nil =>
          simp [pathStrength]
      | cons b t' =>
          have hnot : x ∉ b :: t' := (List.nodup_cons.mp hnodup).1
          have hmargin :
              margin P x b ≤ margin P' x b :=
            margin_le_of_simpleLift_xa (P := P) (P' := P') (x := x) (a := b) hLift
          cases t' with
          | nil =>
              simpa [pathStrength_two] using hmargin
          | cons c t'' =>
              have htail :
                  pathStrength P (b :: c :: t'') =
                    pathStrength P' (b :: c :: t'') := by
                exact pathStrength_eq_of_no_x P P' x hLift (b :: c :: t'') (by
                  simpa using hnot)
              have hle :
                  min (margin P x b) (pathStrength P (b :: c :: t'')) ≤
                    min (margin P' x b) (pathStrength P' (b :: c :: t'')) := by
                refine min_le_min hmargin ?_
                simp [htail]
              simpa [pathStrength_cons_cons_cons, htail] using hle

lemma not_mem_dropLast_of_nodup_getLast? {A : Type} {x : A} {l : List A}
    (hnodup : l.Nodup) (hlast : l.getLast? = some x) :
    x ∉ l.dropLast := by
  have hxmem : x ∈ l.getLast? := by
    simp [hlast]
  have hsplit : l.dropLast ++ [x] = l := by
    simpa using (List.dropLast_append_getLast? (l := l) (a := x) hxmem)
  have hnodup' : (l.dropLast ++ [x]).Nodup := by
    simpa [hsplit] using hnodup
  have hdis : List.Disjoint l.dropLast ([x] : List A) :=
    (List.nodup_append'.1 hnodup').2.2
  exact (List.disjoint_cons_right.mp hdis).1

lemma pathStrength_le_of_last_x {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x : A) (hLift : simpleLift P' P x) :
    ∀ l, l.getLast? = some x → l.Nodup → pathStrength P' l ≤ pathStrength P l := by
  intro l hlast hnodup
  induction l with
  | nil =>
      cases hlast
  | cons a t ih =>
      cases t with
      | nil =>
          simp [pathStrength]
      | cons b t' =>
          cases t' with
          | nil =>
              have hb : b = x := by
                simpa using hlast
              subst b
              have ha : a ≠ x := by
                have hnot : a ∉ ([x] : List A) := (List.nodup_cons.mp hnodup).1
                simpa using hnot
              have hmargin :
                  margin P' a x ≤ margin P a x :=
                margin_le_of_simpleLift_ax (P := P) (P' := P') (x := x) (a := a) hLift
              simpa [pathStrength_two] using hmargin
          | cons c t'' =>
              have hlast_tail : (b :: c :: t'').getLast? = some x := by
                simpa using hlast
              have hnodup_tail : (b :: c :: t'').Nodup :=
                (List.nodup_cons.mp hnodup).2
              have htail :
                  pathStrength P' (b :: c :: t'') ≤
                    pathStrength P (b :: c :: t'') :=
                ih hlast_tail hnodup_tail
              have hxnot : x ∉ (a :: b :: c :: t'').dropLast :=
                not_mem_dropLast_of_nodup_getLast? (l := a :: b :: c :: t'')
                  hnodup hlast
              have ha : a ≠ x := by
                intro hax
                apply hxnot
                simp [List.dropLast, hax]
              have hb : b ≠ x := by
                intro hbx
                apply hxnot
                simp [List.dropLast, hbx]
              have hmargin :
                  margin P' a b = margin P a b := by
                simpa using (margin_eq_of_simpleLift P P' x a b ha hb hLift).symm
              have hle :
                  min (margin P' a b) (pathStrength P' (b :: c :: t'')) ≤
                    min (margin P a b) (pathStrength P (b :: c :: t'')) := by
                refine min_le_min ?_ htail
                exact le_of_eq hmargin
              simpa [pathStrength_cons_cons_cons, hmargin] using hle

lemma strongestPath_le_of_simpleLift_head {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x y : A) (hxy : x ≠ y) (hLift : simpleLift P' P x) :
    strongestPath P x y ≤ strongestPath P' x y := by
  classical
  let paths := pathsUpTo (A := A) (Fintype.card A) x y
  have hne : paths.Nonempty := pathsUpTo_nonempty_of_ne (A := A) x y hxy
  let strengths := paths.image (fun l => pathStrength P l)
  let strengths' := paths.image (fun l => pathStrength P' l)
  have hne_s : strengths.Nonempty := by
    rcases hne with ⟨l, hl⟩
    exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
  have hne_s' : strengths'.Nonempty := by
    rcases hne with ⟨l, hl⟩
    exact ⟨pathStrength P' l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
  have hle : Finset.max' strengths hne_s ≤ Finset.max' strengths' hne_s' := by
    refine (Finset.max'_le_iff _ _).2 ?_
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hprops := path_props_of_mem_pathsUpTo (l := l) (a := x) (b := y) hl
    have hhead : l.head? = some x := hprops.1
    have hnodup : l.Nodup := hprops.2.2.1
    have hle' : pathStrength P l ≤ pathStrength P' l :=
      pathStrength_le_of_head_x P P' x hLift l hhead hnodup
    have hmem' : pathStrength P' l ∈ strengths' :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have hle'' : pathStrength P' l ≤ Finset.max' strengths' hne_s' :=
      Finset.le_max' _ _ hmem'
    exact le_trans hle' hle''
  have hdef : strongestPath P x y = Finset.max' strengths hne_s := by
    simp [strongestPath, paths, strengths, hne]
  have hdef' : strongestPath P' x y = Finset.max' strengths' hne_s' := by
    simp [strongestPath, paths, strengths', hne]
  simpa [hdef, hdef'] using hle

lemma strongestPath_le_of_simpleLift_last {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (x y : A) (hxy : y ≠ x) (hLift : simpleLift P' P x) :
    strongestPath P' y x ≤ strongestPath P y x := by
  classical
  let paths := pathsUpTo (A := A) (Fintype.card A) y x
  have hne : paths.Nonempty := pathsUpTo_nonempty_of_ne (A := A) y x hxy
  let strengths := paths.image (fun l => pathStrength P l)
  let strengths' := paths.image (fun l => pathStrength P' l)
  have hne_s : strengths.Nonempty := by
    rcases hne with ⟨l, hl⟩
    exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
  have hne_s' : strengths'.Nonempty := by
    rcases hne with ⟨l, hl⟩
    exact ⟨pathStrength P' l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
  have hle : Finset.max' strengths' hne_s' ≤ Finset.max' strengths hne_s := by
    refine (Finset.max'_le_iff _ _).2 ?_
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hprops := path_props_of_mem_pathsUpTo (l := l) (a := y) (b := x) hl
    have hlast : l.getLast? = some x := hprops.2.1
    have hnodup : l.Nodup := hprops.2.2.1
    have hle' : pathStrength P' l ≤ pathStrength P l :=
      pathStrength_le_of_last_x P P' x hLift l hlast hnodup
    have hmem' : pathStrength P l ∈ strengths :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have hle'' : pathStrength P l ≤ Finset.max' strengths hne_s :=
      Finset.le_max' _ _ hmem'
    exact le_trans hle' hle''
  have hdef : strongestPath P y x = Finset.max' strengths hne_s := by
    simp [strongestPath, paths, strengths, hne]
  have hdef' : strongestPath P' y x = Finset.max' strengths' hne_s' := by
    simp [strongestPath, paths, strengths', hne]
  simpa [hdef, hdef'] using hle

theorem schulze_monotonicity : Monotonicity schulze := by
  intro V A _ _ P P' x hx hLift
  classical
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ x, ?_⟩
  intro y hy
  by_cases hxy : y = x
  · subst y
    have hnot : ¬ schulzeDefeats P' x x := by
      simp [schulzeDefeats]
    exact hnot hy
  · have hy' : strongestPath P' y x > strongestPath P' x y := by
      simpa [schulzeDefeats] using hy
    have hle_yx : strongestPath P' y x ≤ strongestPath P y x :=
      strongestPath_le_of_simpleLift_last P P' x y hxy hLift
    have hle_xy : strongestPath P x y ≤ strongestPath P' x y :=
      strongestPath_le_of_simpleLift_head P P' x y (by exact ne_comm.mp hxy) hLift
    have hlt1 : strongestPath P x y < strongestPath P' y x :=
      lt_of_le_of_lt hle_xy hy'
    have hlt2 : strongestPath P x y < strongestPath P y x :=
      lt_of_lt_of_le hlt1 hle_yx
    have hyP : schulzeDefeats P y x := by
      simpa [schulzeDefeats] using hlt2
    have hxcond : ∀ z, ¬ schulzeDefeats P z x := (Finset.mem_filter.mp hx).2
    exact (hxcond y) hyP

end SocialChoice
