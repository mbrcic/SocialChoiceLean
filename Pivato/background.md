# Background for Pivato Formalization

## Scope and Feasibility

This project is feasible in Lean 4/mathlib and in this repository, but it is substantial.

- High-confidence feasible: formalizing Pivato's abstract signal-profile framework and Theorem 1 (reinforcement implies balance, and converse).
- Higher risk/heavier effort: Theorem 2 path, especially Appendix C.8 style combinatorics and symmetry averaging.
- Best strategy: formalize the abstract theory first, then add a bridge to existing `SocialChoice` profile-based rules.


## Relevant Mathlib Content

The core technology needed by the paper is largely present.

- Finite-support profiles:
  - `Finsupp` and additive/group structure.
  - Files: `Mathlib/Data/Finsupp/Defs.lean`, `Mathlib/Algebra/Group/Finsupp.lean`.
- Quotients of additive groups:
  - `QuotientAddGroup.mk`, `QuotientAddGroup.lift`, quotient additive group instances.
  - Files: `Mathlib/GroupTheory/QuotientGroup/Defs.lean`, `Mathlib/GroupTheory/QuotientGroup/Basic.lean`.
- General order extension:
  - `extend_partialOrder` (Szpilrajn-style extension for partial orders).
  - File: `Mathlib/Order/Extension/Linear.lean`.
- Lexicographic order support:
  - `Pi.Lex`, `Finsupp.Lex`, `DFinsupp.Lex`, and ordered-additive compatibility lemmas.
  - Files: `Mathlib/Order/PiLex.lean`, `Mathlib/Data/Finsupp/Lex.lean`,
    `Mathlib/Data/DFinsupp/Lex.lean`, `Mathlib/Algebra/Order/Group/PiLex.lean`.
- Torsion-free/divisible ingredients:
  - `IsAddTorsionFree`, `nsmul_right_injective`, `zsmul_right_injective`.
  - `QuotientAddGroup.instIsAddTorsionFree` (for quotient by torsion subgroup).
  - `DivisibleBy` and quotient divisibility (`QuotientAddGroup.divisibleBy` via `to_additive`).
  - Files: `Mathlib/Algebra/Group/Defs.lean`, `Mathlib/Algebra/Group/Torsion.lean`,
    `Mathlib/GroupTheory/Torsion.lean`, `Mathlib/GroupTheory/Divisible.lean`.
- Group actions, orbits, and transitivity:
  - `MulAction.orbit`, `orbitRel.Quotient`, `MulAction.univ_eq_iUnion_orbit`.
  - `MulAction.IsMultiplyPretransitive`, `MulAction.is_two_pretransitive_iff`.
  - Files: `Mathlib/GroupTheory/GroupAction/Defs.lean`,
    `Mathlib/GroupTheory/GroupAction/MultipleTransitivity.lean`.


## Important API Note (Current Mathlib Snapshot)

Older bundled class names are no longer used as classes in current mathlib:

- `OrderedAddCommGroup` / `LinearOrderedAddCommGroup` are not the main class interfaces now.
- Prefer assumptions like:
  - `[AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]`
  - and related unbundled monotonicity/cancellation classes.
- See: `Mathlib/Algebra/Order/Group/Defs.lean`.


## Custom Development Expected (Main Gaps)

These are the parts likely not directly available as ready-made lemmas:

- Pivato's homogeneous preorder/conoid framework as a reusable Lean layer.
- A "homogeneous Szpilrajn" extension statement (order extension preserving additive homogeneity).
- Some quotient-order transfer lemmas tailored to the paper's construction.
- Appendix C.3/C.8 combinatorial machinery (finite permutation orbit arguments and equation packings).


## Recommended Formalization Plan

1. Create a standalone abstract layer under `Pivato/`.
2. Define abstract objects:
   - signal type `V`, alternatives `X`,
   - profile domain as subsets of `V →₀ ℕ`,
   - abstract voting correspondences.
3. Formalize reinforcement and balance systems in the abstract layer.
4. Prove Theorem 1 first (the first major milestone).
5. Add neutrality via group actions (`ν : Perm X → Perm V`) and equivariance.
6. Build the scoring-system side and the balance-to-scoring equivalence conditions.
7. Tackle Theorem 2 (expect most effort in C.8-like combinatorics).
8. Add a bridge file from `SocialChoice.Profile` to abstract ballot-count representation.


## Bridge Back to Existing SocialChoiceLean

The repo already has useful infrastructure for the eventual bridge:

- Variable-electorate machinery (`Electorate`, `restrictElectorate`):
  - `SocialChoice/Axioms/Participation.lean`.
- Reinforcement axiom in disjoint-electorate form:
  - `SocialChoice/Axioms/Reinforcement.lean`.
- Existing scoring/reinforcement proofs for concrete rules:
  - `SocialChoice/Rules/ScoringRules/Reinforcement.lean`.

So the recommended architecture is:

- `Pivato/` for abstract theorem development.
- A later bridge layer to connect abstract counting semantics with existing profile semantics.
