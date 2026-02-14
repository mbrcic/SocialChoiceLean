import Pivato.Theorem2.C8Setup
import Pivato.Theorem1.PairwiseOrders

/-!
# Lemma C.8 claims C.8.1 and C.8.2

This file isolates the first two claims in the Appendix-C.8 pipeline.
-/

namespace Pivato

section C8Claims12

universe uV uX uI

variable {V : Type uV} {X : Type uX} {ι : Type uI}

/-- Claim C.8.1 (abstracted form):
block-filtered orbit domains are cones under reinforcement and cone-domain
assumptions. -/
theorem claimC81_orbitBlock_isCone
    [DecidableEq X]
    {D : Domain V} {F : RuleOn D X}
    (hCone : IsCone D)
    (hR : Reinforcement D F)
    (hNE : NonemptyOnDomain D F)
    (orbitMap : NProfile V → NProfile V)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D)
    (hOrbitAdd : ∀ d e, orbitMap (d + e) = orbitMap d + orbitMap e)
    (hOrbitNsmul : ∀ (n : ℕ) d, orbitMap (n • d) = n • orbitMap d)
    (block : Set X) :
    IsCone (orbitBlockDomain D F orbitMap horbit block) := by
  refine ⟨?_, ?_⟩
  · intro d e hd he
    rcases hd with ⟨hdD, hBlockD⟩
    rcases he with ⟨heD, hBlockE⟩
    have hdeD : d + e ∈ D := hCone.1 hdD heD
    refine ⟨hdeD, ?_⟩
    intro x hxBlock
    by_cases hBlock : block.Nonempty
    · obtain ⟨w, hwBlock⟩ := hBlock
      have hwD : w ∈ F ⟨orbitMap d, horbit hdD⟩ := hBlockD hwBlock
      have hwE : w ∈ F ⟨orbitMap e, horbit heD⟩ := hBlockE hwBlock
      have hInter :
          (F ⟨orbitMap d, horbit hdD⟩ ∩ F ⟨orbitMap e, horbit heD⟩).Nonempty :=
        ⟨w, hwD, hwE⟩
      have hSumOrbitD : orbitMap d + orbitMap e ∈ D := hCone.1 (horbit hdD) (horbit heD)
      have hEq :
          F ⟨orbitMap d + orbitMap e, hSumOrbitD⟩ =
            F ⟨orbitMap d, horbit hdD⟩ ∩ F ⟨orbitMap e, horbit heD⟩ :=
        hR.2 (horbit hdD) (horbit heD) hSumOrbitD hInter
      have hxInter :
          x ∈ F ⟨orbitMap d, horbit hdD⟩ ∩ F ⟨orbitMap e, horbit heD⟩ :=
        ⟨hBlockD hxBlock, hBlockE hxBlock⟩
      have hxSum : x ∈ F ⟨orbitMap d + orbitMap e, hSumOrbitD⟩ := by
        simpa [hEq] using hxInter
      have hSub :
          (⟨orbitMap (d + e), horbit hdeD⟩ : {d : NProfile V // d ∈ D}) =
            ⟨orbitMap d + orbitMap e, hSumOrbitD⟩ := by
        apply Subtype.ext
        simp [hOrbitAdd d e]
      simpa [hSub] using hxSum
    · exact False.elim (hBlock ⟨x, hxBlock⟩)
  · intro d n hn hnd
    rcases hnd with ⟨hndD, hBlockN⟩
    have hdD : d ∈ D := hCone.2 hn hndD
    refine ⟨hdD, ?_⟩
    intro x hxBlock
    by_cases hBlock : block.Nonempty
    · by_contra hxNot
      have huD : orbitMap d ∈ D := horbit hdD
      rcases hNE ⟨orbitMap d, huD⟩ with ⟨y, hyWin⟩
      rcases winner_loser_nsmul_of_reinforcement
          (hR := hR) (x := y) (y := x) (d := orbitMap d) (hd := huD) hyWin hxNot hn with
        ⟨hnuD, _hyN, hxNotN⟩
      have hxN : x ∈ F ⟨orbitMap (n • d), horbit hndD⟩ := hBlockN hxBlock
      have hSub :
          (⟨orbitMap (n • d), horbit hndD⟩ : {d : NProfile V // d ∈ D}) =
            ⟨n • orbitMap d, hnuD⟩ := by
        apply Subtype.ext
        simp [hOrbitNsmul n d]
      exact hxNotN (by simpa [hSub] using hxN)
    · exact False.elim (hBlock ⟨x, hxBlock⟩)

/-- Claim C.8.2 (abstracted form):
if every profile's orbit-image winners contain at least one block in the
family, then the original domain is the union of the corresponding block
domains. -/
theorem claimC82_cover_by_orbitBlocks
    {D : Domain V} {F : RuleOn D X}
    (orbitMap : NProfile V → NProfile V)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D)
    (blocks : ι → Set X)
    (hCover :
      ∀ d : NProfile V, ∀ hd : d ∈ D,
        ∃ i : ι, blocks i ⊆ F ⟨orbitMap d, horbit hd⟩) :
    D = ⋃ i : ι, orbitBlockDomain D F orbitMap horbit (blocks i) := by
  ext d
  constructor
  · intro hd
    rcases hCover d hd with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨hd, hi⟩⟩
  · intro hd
    rcases Set.mem_iUnion.mp hd with ⟨i, hdi⟩
    exact hdi.1

end C8Claims12

end Pivato
