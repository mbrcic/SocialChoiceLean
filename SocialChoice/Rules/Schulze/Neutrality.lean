import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Max
import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.Schulze.Defs

namespace SocialChoice

open Finset

namespace List

@[simp] lemma head?_map {α β : Type} (f : α → β) (l : List α) :
    (l.map f).head? = l.head?.map f := by
  cases l <;> rfl

@[simp] lemma getLast?_map {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).getLast? = l.getLast?.map f
  | [] => rfl
  | a :: t =>
      by
        cases t with
        | nil => rfl
        | cons b t' =>
            simpa using (getLast?_map f (b :: t'))

end List

section

variable {V A : Type} [Fintype V] [Fintype A]

lemma mem_listsOfLength_map_perm_iff (n : Nat) (σ : Equiv.Perm A) (l : List A) :
    l ∈ listsOfLength (A := A) n ↔ l.map σ.symm ∈ listsOfLength (A := A) n := by
  classical
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨f, _hf, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨σ.symm ∘ f, by simp, ?_⟩
    simp
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨f, _hf, hf⟩
    have hl' : l = (List.ofFn f).map σ := by
      calc
        l = (l.map σ.symm).map σ := by simp [List.map_map]
        _ = (List.ofFn f).map σ := by simp [hf]
    refine Finset.mem_image.mpr ?_
    refine ⟨σ ∘ f, by simp, ?_⟩
    -- `map σ (ofFn f) = ofFn (σ ∘ f)`.
    have : (List.ofFn f).map σ = List.ofFn (σ ∘ f) := by
      simp
    -- Now close.
    simp [hl', this]

lemma mem_pathsOfLength_map_symm_iff (n : Nat) (σ : Equiv.Perm A)
    (a b : A) (l : List A) :
    l ∈ pathsOfLength (A := A) n (σ a) (σ b) ↔
      l.map σ.symm ∈ pathsOfLength (A := A) n a b := by
  classical
  constructor
  · intro hl
    rcases Finset.mem_filter.mp hl with ⟨hlLen, hlProps⟩
    rcases hlProps with ⟨hlen, hhead, hlast, hnodup⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · -- membership in `listsOfLength`
      exact (mem_listsOfLength_map_perm_iff (n := n) (σ := σ) (l := l)).1 hlLen
    · -- filter conditions
      refine ⟨by simpa [List.length_map] using hlen, ?_, ?_, ?_⟩
      · -- head?
        simpa [Option.map_map] using congrArg (fun t => t.map σ.symm) hhead
      · -- getLast?
        simpa [Option.map_map] using congrArg (fun t => t.map σ.symm) hlast
      · -- Nodup
        exact List.Nodup.map σ.symm.injective hnodup
  · intro hl
    rcases Finset.mem_filter.mp hl with ⟨hlLen, hlProps⟩
    rcases hlProps with ⟨hlen, hhead, hlast, hnodup⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · -- membership in `listsOfLength`
      have : l.map σ.symm ∈ listsOfLength (A := A) n := hlLen
      -- apply the forward direction with `σ.symm` and rewrite
      have := (mem_listsOfLength_map_perm_iff (n := n) (σ := σ.symm) (l := l.map σ.symm)).1 this
      simpa [List.map_map] using this
    · -- filter conditions
      refine ⟨by simpa [List.length_map] using hlen, ?_, ?_, ?_⟩
      · -- head?
        have := congrArg (fun t => t.map σ) hhead
        simpa [Option.map_map] using this
      · -- getLast?
        have := congrArg (fun t => t.map σ) hlast
        simpa [Option.map_map] using this
      · -- Nodup
        -- map back along `σ`
        have h' : ((l.map σ.symm).map σ).Nodup := List.Nodup.map σ.injective hnodup
        simpa [List.map_map] using h'

lemma mem_pathsUpTo_map_symm_iff (σ : Equiv.Perm A) (a b : A) (l : List A) :
    l ∈ pathsUpTo (A := A) (Fintype.card A) (σ a) (σ b) ↔
      l.map σ.symm ∈ pathsUpTo (A := A) (Fintype.card A) a b := by
  classical
  -- unfold `pathsUpTo` only; keep `pathsOfLength` abstract via the previous lemma
  simp [pathsUpTo, mem_pathsOfLength_map_symm_iff (σ := σ) (a := a) (b := b)]

lemma pathMargins_permuteCandidates (P : Profile V A) (σ : Equiv.Perm A) :
    ∀ l : List A,
      pathMargins (V := V) (A := A) (permuteCandidates P σ) l =
        pathMargins P (l.map σ.symm)
  | [] => by simp [pathMargins]
  | [a] => by simp [pathMargins]
  | a :: b :: t => by
      simp [pathMargins, margin_permuteCandidates, pathMargins_permuteCandidates P σ (b :: t)]

lemma pathStrength_permuteCandidates (P : Profile V A) (σ : Equiv.Perm A) (l : List A) :
    pathStrength (V := V) (A := A) (permuteCandidates P σ) l = pathStrength P (l.map σ.symm) := by
  classical
  calc
    pathStrength (permuteCandidates P σ) l =
        minList (pathMargins (permuteCandidates P σ) l) := by
          simpa using (pathStrength_eq_minList (P := permuteCandidates P σ) l)
    _ = minList (pathMargins P (l.map σ.symm)) := by
          simp [pathMargins_permuteCandidates (P := P) (σ := σ)]
    _ = pathStrength P (l.map σ.symm) := by
          symm
          simpa using (pathStrength_eq_minList (P := P) (l := l.map σ.symm))

lemma strongestPath_permuteCandidates (P : Profile V A) (σ : Equiv.Perm A) (a b : A) :
    strongestPath (V := V) (A := A) (permuteCandidates P σ) (σ a) (σ b) =
      strongestPath P a b := by
  classical
  -- Name the path sets explicitly so we can reason about them.
  let paths : Finset (List A) := pathsUpTo (A := A) (Fintype.card A) a b
  let paths' : Finset (List A) := pathsUpTo (A := A) (Fintype.card A) (σ a) (σ b)
  by_cases hne : paths.Nonempty
  · have hne' : paths'.Nonempty := by
      rcases hne with ⟨l, hl⟩
      refine ⟨l.map σ, ?_⟩
      have hl' : (l.map σ).map σ.symm ∈ paths := by
        simpa [List.map_map] using hl
      exact (mem_pathsUpTo_map_symm_iff (σ := σ) (a := a) (b := b) (l := l.map σ)).2 hl'
    -- Compare the sets of path strengths.
    let strengths : Finset Int := paths.image (fun l => pathStrength P l)
    let strengths' : Finset Int := paths'.image (fun l => pathStrength (permuteCandidates P σ) l)
    have hstrengths : strengths.Nonempty := by
      rcases hne with ⟨l, hl⟩
      exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    have hstrengths' : strengths'.Nonempty := by
      rcases hne' with ⟨l, hl⟩
      exact ⟨pathStrength (permuteCandidates P σ) l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    have hstrengths_eq : strengths' = strengths := by
      apply Finset.ext
      intro s
      constructor
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨l, hl, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨l.map σ.symm, (mem_pathsUpTo_map_symm_iff (σ := σ) (a := a) (b := b) (l := l)).1 hl, ?_⟩
        simpa using (pathStrength_permuteCandidates (P := P) (σ := σ) (l := l)).symm
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨l, hl, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨l.map σ, ?_, ?_⟩
        · have : (l.map σ).map σ.symm ∈ paths := by
            simpa [List.map_map] using hl
          exact (mem_pathsUpTo_map_symm_iff (σ := σ) (a := a) (b := b) (l := l.map σ)).2 this
        · have : pathStrength (permuteCandidates P σ) (l.map σ) = pathStrength P l := by
            simpa [List.map_map] using (pathStrength_permuteCandidates (P := P) (σ := σ) (l := l.map σ))
          simp [this]
    -- With equal strength sets, the maxima agree.
    have hmax :
        Finset.max' strengths' hstrengths' = Finset.max' strengths hstrengths := by
      apply le_antisymm
      · refine Finset.max'_le _ _ _ ?_
        intro x hx
        have hx' : x ∈ strengths := by simpa [hstrengths_eq] using hx
        exact Finset.le_max' _ _ hx'
      · refine Finset.max'_le _ _ _ ?_
        intro x hx
        have hx' : x ∈ strengths' := by simpa [hstrengths_eq] using hx
        exact Finset.le_max' _ _ hx'
    simp [strongestPath, hne, hne', strengths, strengths', hmax, paths, paths']
  · have hne' : ¬ paths'.Nonempty := by
      intro hne'
      rcases hne' with ⟨l, hl⟩
      have : l.map σ.symm ∈ paths := (mem_pathsUpTo_map_symm_iff (σ := σ) (a := a) (b := b) (l := l)).1 hl
      exact hne ⟨l.map σ.symm, this⟩
    simp [strongestPath, paths, paths', hne, hne', margin_permuteCandidates]

lemma schulzeDefeats_permuteCandidates (P : Profile V A) (σ : Equiv.Perm A) (a b : A) :
    schulzeDefeats (V := V) (A := A) (permuteCandidates P σ) (σ a) (σ b) ↔
      schulzeDefeats P a b := by
  simp [schulzeDefeats, strongestPath_permuteCandidates (P := P) (σ := σ)]

theorem schulze_neutrality : Neutrality schulze := by
  intro V A _ _ P σ
  classical
  apply Finset.ext
  intro c
  constructor
  · intro hc
    dsimp [permuteWinners] at hc
    rcases Finset.mem_map.mp hc with ⟨a, ha, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp, ?_⟩
    intro b hb
    have ha_cond : ∀ b, ¬ schulzeDefeats P b a := (Finset.mem_filter.mp ha).2
    have hiff :
        schulzeDefeats (permuteCandidates P σ) b (σ a) ↔
          schulzeDefeats P (σ.symm b) a := by
      simpa using (schulzeDefeats_permuteCandidates (P := P) (σ := σ) (a := σ.symm b) (b := a))
    exact ha_cond (σ.symm b) (hiff.1 hb)
  · intro hc
    have hc_cond : ∀ b, ¬ schulzeDefeats (permuteCandidates P σ) b c := (Finset.mem_filter.mp hc).2
    have ha : σ.symm c ∈ schulze P := by
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      intro b hb
      have hiff :
          schulzeDefeats (permuteCandidates P σ) (σ b) c ↔ schulzeDefeats P b (σ.symm c) := by
        simpa using (schulzeDefeats_permuteCandidates (P := P) (σ := σ) (a := b) (b := σ.symm c))
      exact hc_cond (σ b) (hiff.2 hb)
    have : c ∈ (schulze P).map σ.toEmbedding := by
      exact Finset.mem_map.mpr ⟨σ.symm c, ha, by simp⟩
    simpa [permuteWinners] using this

end

end SocialChoice
