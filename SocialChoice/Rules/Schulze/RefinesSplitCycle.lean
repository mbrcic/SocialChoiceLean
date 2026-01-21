import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.SplitCycle.Clones

namespace SocialChoice

private lemma isChain_of_le_pathStrength {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (m : Int) :
    ∀ l, m ≤ pathStrength P l →
      List.IsChain (fun a b => m ≤ margin P a b) l
  | [], _ => by
      simp
  | [a], _ => by
      simp
  | a :: b :: t, h => by
      cases t with
      | nil =>
          have hrel : m ≤ margin P a b := by
            simpa [pathStrength_two] using h
          exact (List.isChain_cons_cons).2 ⟨hrel, by simp⟩
      | cons c t' =>
          have hstrength :
              pathStrength P (a :: b :: c :: t') =
                min (margin P a b) (pathStrength P (b :: c :: t')) :=
            pathStrength_cons_cons_cons (P := P) a b c t'
          have h' : m ≤ min (margin P a b) (pathStrength P (b :: c :: t')) := by
            simpa [hstrength] using h
          have hrel : m ≤ margin P a b := (le_min_iff.mp h').1
          have htail : m ≤ pathStrength P (b :: c :: t') := (le_min_iff.mp h').2
          have hchain_tail :=
            isChain_of_le_pathStrength (P := P) (m := m) (l := b :: c :: t') htail
          exact (List.isChain_cons_cons).2 ⟨hrel, hchain_tail⟩

lemma splitCycleDefeats_imp_schulzeDefeats {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {x y : A} :
    splitCycleDefeats P x y → schulzeDefeats P x y := by
  intro hdef
  rcases (splitCycleDefeats_iff_path (P := P) (x := x) (y := y)).1 hdef with ⟨hpos, hnoPath⟩
  have hne : x ≠ y := ne_of_margin_pos hpos
  have hxy_ge : margin P x y ≤ strongestPath P x y :=
    margin_le_strongestPath_of_ne (P := P) (a := x) (b := y) hne
  have hlt : strongestPath P y x < margin P x y := by
    by_contra hle
    have hle' : margin P x y ≤ strongestPath P y x := not_lt.mp hle
    have hne_paths :
        (pathsUpTo (A := A) (Fintype.card A) y x).Nonempty :=
      pathsUpTo_nonempty_of_ne (A := A) y x hne.symm
    rcases exists_max_path_props (P := P) (a := y) (b := x) hne_paths with
      ⟨l, _hl, hhead, hlast, hnodup, hlen, hstrength⟩
    have hne_l : l ≠ [] := by
      intro hnil
      simp [hnil] at hlen
    have hfirst : l[0]'(List.length_pos_of_ne_nil hne_l) = y := by
      have hhead' : l.head hne_l = y := by
        have hhead_eq : l.head? = some (l.head hne_l) :=
          List.head?_eq_some_head (l := l) hne_l
        have : some (l.head hne_l) = some y := by
          simpa [hhead_eq] using hhead
        exact Option.some.inj this
      simpa [List.head_eq_getElem_zero] using hhead'
    have hlast' : l.getLast hne_l = x := by
      have hlast_eq : l.getLast? = some (l.getLast hne_l) :=
        List.getLast?_eq_some_getLast (l := l) hne_l
      have : some (l.getLast hne_l) = some x := by
        simpa [hlast_eq] using hlast
      exact Option.some.inj this
    have hle_path : margin P x y ≤ pathStrength P l := by
      simpa [hstrength] using hle'
    have hchain :
        List.IsChain (fun a b => margin P x y ≤ margin P a b) l :=
      isChain_of_le_pathStrength (P := P) (m := margin P x y) (l := l) hle_path
    exact hnoPath ⟨l, hne_l, hnodup, hfirst, hlast', hchain⟩
  exact lt_of_lt_of_le hlt hxy_ge

lemma schulze_subset_splitCycle {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) :
    schulze P ⊆ splitCycle P := by
  classical
  intro a ha
  have hcond : ∀ b, ¬ schulzeDefeats P b a := (Finset.mem_filter.mp ha).2
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ a, ?_⟩
  intro b hdef
  have hsch : schulzeDefeats P b a := splitCycleDefeats_imp_schulzeDefeats (P := P) hdef
  exact (hcond b) hsch

end SocialChoice
