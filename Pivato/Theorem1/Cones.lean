import Pivato.Rules

/-!
# Theorem 1 core: winner cones

This file introduces the `C_x` winner cones and proves additive closure of
`C_x` under reinforcement.
-/

namespace Pivato

section WinnerCones

variable {V X : Type*} {D : Domain V}

/-- `Wins F x d` means `x` is selected by rule `F` at profile `d`. -/
def Wins (F : RuleOn D X) (x : X) (d : NProfile V) : Prop :=
  ∃ hd : d ∈ D, x ∈ F ⟨d, hd⟩

lemma wins_proof_irrel {F : RuleOn D X} {x : X} {d : NProfile V}
    {hd₁ hd₂ : d ∈ D} :
    x ∈ F ⟨d, hd₁⟩ ↔ x ∈ F ⟨d, hd₂⟩ := by
  have hsub : (⟨d, hd₁⟩ : {d : NProfile V // d ∈ D}) = ⟨d, hd₂⟩ := by
    apply Subtype.ext
    rfl
  simp [hsub]

lemma wins_mk {F : RuleOn D X} {x : X} {d : NProfile V} {hd : d ∈ D}
    (hx : x ∈ F ⟨d, hd⟩) : Wins F x d :=
  ⟨hd, hx⟩

/-- Winner cone `C_x = {d ∈ D | x ∈ F(d)}`. -/
def winnerCone (F : RuleOn D X) (x : X) : Set (NProfile V) :=
  {d | Wins F x d}

lemma mem_winnerCone_iff {F : RuleOn D X} {x : X} {d : NProfile V} :
    d ∈ winnerCone F x ↔ Wins F x d :=
  Iff.rfl

lemma winnerCone_zero_of_generalAbstention {F : RuleOn D X} (hD : IsDomain D)
    (hA : GeneralAbstention D F) (x : X) :
    (0 : NProfile V) ∈ winnerCone F x := by
  refine ⟨hD, ?_⟩
  simp [hA hD]

lemma winnerCone_add_closed_of_reinforcement {F : RuleOn D X}
    (hR : Reinforcement D F) (x : X) :
    ∀ ⦃d e : NProfile V⦄,
      d ∈ winnerCone F x → e ∈ winnerCone F x → d + e ∈ winnerCone F x := by
  intro d e hd he
  rcases hd with ⟨hdD, hxd⟩
  rcases he with ⟨heD, hxe⟩
  have hinter : (F ⟨d, hdD⟩ ∩ F ⟨e, heD⟩).Nonempty := ⟨x, ⟨hxd, hxe⟩⟩
  have hsum : d + e ∈ D := hR.1 hdD heD hinter
  have hEq : F ⟨d + e, hsum⟩ = F ⟨d, hdD⟩ ∩ F ⟨e, heD⟩ := hR.2 hdD heD hsum hinter
  refine ⟨hsum, ?_⟩
  have hxinter : x ∈ F ⟨d, hdD⟩ ∩ F ⟨e, heD⟩ := ⟨hxd, hxe⟩
  simpa [hEq] using hxinter

end WinnerCones

end Pivato
