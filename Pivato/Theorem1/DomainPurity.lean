import Pivato.Theorem1.Cones

/-!
# Domain-purity scaling lemmas for Theorem 1

This file isolates reinforcement consequences used by the corrected paper-facing
packaging: under nonemptiness, reinforcement is invariant under positive
profile scaling; with domain purity/divisibility, winner cones inherit the same
positive-scaling divisibility property.
-/

namespace Pivato

section DomainPurity

variable {V X : Type*} {D : Domain V} {F : RuleOn D X}

/-- Under reinforcement + nonemptiness, positive profile multiples are in-domain,
and winners at `n • d` coincide with winners at `d`. -/
lemma reinforcement_nsmul_mem_and_eq
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    {d : NProfile V} (hd : d ∈ D) :
    ∀ {n : ℕ}, n ≠ 0 →
      ∃ hnd : n • d ∈ D, F ⟨n • d, hnd⟩ = F ⟨d, hd⟩ := by
  let haux :
      ∀ k : ℕ,
        ∃ hk : (k + 1) • d ∈ D, F ⟨(k + 1) • d, hk⟩ = F ⟨d, hd⟩ := by
    intro k
    induction k with
    | zero =>
        have h1D : (0 + 1) • d ∈ D := by
          simpa using hd
        refine ⟨h1D, ?_⟩
        have hsub : (⟨(0 + 1) • d, h1D⟩ : {d : NProfile V // d ∈ D}) = ⟨d, hd⟩ := by
          apply Subtype.ext
          simp
        simp
    | succ k ih =>
        rcases ih with ⟨hkD, hkEq⟩
        rcases hNE ⟨d, hd⟩ with ⟨x, hxd⟩
        have hxk : x ∈ F ⟨(k + 1) • d, hkD⟩ := by
          simpa [hkEq] using hxd
        have hinter :
            (F ⟨d, hd⟩ ∩ F ⟨(k + 1) • d, hkD⟩).Nonempty := ⟨x, hxd, hxk⟩
        have hsumD : d + (k + 1) • d ∈ D := hR.1 hd hkD hinter
        have hsumEq :
            F ⟨d + (k + 1) • d, hsumD⟩ = F ⟨d, hd⟩ := by
          calc
            F ⟨d + (k + 1) • d, hsumD⟩
                = F ⟨d, hd⟩ ∩ F ⟨(k + 1) • d, hkD⟩ := hR.2 hd hkD hsumD hinter
            _ = F ⟨d, hd⟩ := by
              ext y
              constructor
              · intro hy
                exact hy.1
              · intro hy
                exact ⟨hy, by simpa [hkEq] using hy⟩
        have hsmul : d + (k + 1) • d = (k + 2) • d := by
          simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using
            (succ_nsmul' d (k + 1)).symm
        have hnextD : (k + 2) • d ∈ D := by
          simpa [hsmul] using hsumD
        refine ⟨hnextD, ?_⟩
        have hsub :
            (⟨(k + 2) • d, hnextD⟩ : {d : NProfile V // d ∈ D}) =
              ⟨d + (k + 1) • d, hsumD⟩ := by
          apply Subtype.ext
          simp [hsmul]
        simpa [hsub] using hsumEq
  intro n hn
  cases n with
  | zero =>
      cases hn rfl
  | succ k =>
      simpa [Nat.succ_eq_add_one] using haux k

/-- Under reinforcement + nonemptiness, every positive multiple of an in-domain
profile is in-domain. -/
lemma domain_nsmul_mem_of_reinforcement_nonempty
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    {d : NProfile V} (hd : d ∈ D)
    {n : ℕ} (hn : n ≠ 0) :
    n • d ∈ D := by
  rcases reinforcement_nsmul_mem_and_eq (F := F) hR hNE hd hn with ⟨hnd, _⟩
  exact hnd

/-- Under reinforcement + nonemptiness, winners are unchanged by positive
profile scaling. -/
lemma reinforcement_eq_at_nsmul
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    {d : NProfile V} (hd : d ∈ D)
    {n : ℕ} (hn : n ≠ 0)
    {hnd : n • d ∈ D} :
    F ⟨n • d, hnd⟩ = F ⟨d, hd⟩ := by
  rcases reinforcement_nsmul_mem_and_eq (F := F) hR hNE hd hn with ⟨hnd', hEq⟩
  have hsub : (⟨n • d, hnd'⟩ : {d : NProfile V // d ∈ D}) = ⟨n • d, hnd⟩ := by
    apply Subtype.ext
    rfl
  simpa [hsub] using hEq

/-- Winner cones inherit divisibility from domain purity, using reinforcement
and nonemptiness to identify winners across positive profile multiples. -/
lemma winnerCone_divisible_of_domainDivisible
    (hPure : DomainDivisible D)
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    (x : X) :
    ∀ {d : NProfile V} {n : ℕ},
      n ≠ 0 → n • d ∈ winnerCone F x → d ∈ winnerCone F x := by
  intro d n hn hndWin
  rcases hndWin with ⟨hndD, hxnd⟩
  have hd : d ∈ D := hPure hn hndD
  have hEq : F ⟨n • d, hndD⟩ = F ⟨d, hd⟩ :=
    reinforcement_eq_at_nsmul (F := F) hR hNE hd hn
  refine ⟨hd, ?_⟩
  simpa [hEq] using hxnd

/-- `IsCone` provides the purity assumption used above. -/
lemma winnerCone_divisible_of_isCone
    (hCone : IsCone D)
    (hR : Reinforcement D F) (hNE : NonemptyOnDomain D F)
    (x : X) :
    ∀ {d : NProfile V} {n : ℕ},
      n ≠ 0 → n • d ∈ winnerCone F x → d ∈ winnerCone F x :=
  winnerCone_divisible_of_domainDivisible (F := F) (isCone_divisible hCone) hR hNE x

end DomainPurity

end Pivato
