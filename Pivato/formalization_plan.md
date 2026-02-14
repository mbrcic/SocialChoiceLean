# Pivato Formalization Plan

This document records a concrete roadmap for continuing the formalization of Pivato's paper in `Pivato/`.

Current baseline (as of February 11, 2026):
- Appendix B infrastructure is formalized in:
  - `Pivato/HomogeneousSzpilrajn.lean`
  - `Pivato/AppendixB.lean`
- These files compile cleanly and provide the core order-extension machinery needed later.
- Abstract layers and initial Theorem 1 files are now implemented and compile:
  - `Pivato/Core.lean`
  - `Pivato/Profiles.lean`
  - `Pivato/Rules.lean`
  - `Pivato/Scoring.lean`
  - `Pivato/Balance.lean`
  - `Pivato/Theorem1/Cones.lean`
  - `Pivato/Theorem1/PairwiseOrders.lean`
  - `Pivato/Theorem1/Representation.lean`

## Scope and Strategy

The most effective sequence is:
1. Stabilize an abstract framework for count profiles, domains, and abstract rules.
2. Build scoring/balance semantics on top of this framework.
3. Formalize the Theorem 1 core construction (winner cones, pairwise difference cones, relation scaffolding, quotient scaffolding).
4. Complete Theorem 1 proof.
5. Add Section 3 neutrality machinery (Lemma C.2, Proposition 1, Proposition 2).
6. Complete Theorem 2 path (C.4--C.8).
7. Add bridge theorems to existing `SocialChoice` profile-based rules.

Reason for this order:
- Theorem 1 is the first major correctness milestone.
- Section 3 and Theorem 2 depend on stable abstract definitions and Theorem 1 proof patterns.
- The bridge layer should come after abstract machinery settles, to avoid repeated refactors.

## File Architecture

Planned architecture:

```text
Pivato/
  Core.lean
  Profiles.lean
  Rules.lean
  Scoring.lean
  Balance.lean
  Theorem1/
    Cones.lean
    PairwiseOrders.lean
    OrderedAdditiveExtension.lean
    C1OrderedCodomain.lean
    Representation.lean
    Skewification.lean
    Main.lean
  Neutrality/
    Defs.lean
    LemmaC2.lean
    Proposition1.lean
    Proposition2.lean
  Theorem2/
    C4_C5.lean
    C6_C7.lean
    C8Orbit.lean
    Main.lean
  Bridge/
    CountProfiles.lean
    ReinforcementBridge.lean
    ScoringBridge.lean
```

Current implementation status:
- Implemented: `Core` through `Theorem1/Main`, including a Stage-D constructive
  reinforcement-to-balance representation theorem and a structured converse
  reinforcement theorem under explicit balance assumptions, now with explicit
  packaging wrappers in `Theorem1/Packaging.lean`.
- Implemented (Stage E start): generalized-neutrality base layer in
  `Neutrality/Defs.lean` and Lemma C.2 transport lemmas in
  `Neutrality/LemmaC2.lean`, plus Proposition 1 and Proposition 2
  theorem files (`Neutrality/Proposition1.lean`,
  `Neutrality/Proposition2.lean`).
- Not yet implemented: Theorem 2 files, bridge files.

## Lean Modeling Decisions

### 1) Profiles and domains

Paper notation:
- `N^{<V>}` and `Z^{<V>}` for finitely supported functions.

Lean representation:
- `NProfile V := V →₀ ℕ`
- `ZProfile V := V →₀ ℤ`
- `Domain V := Set (NProfile V)`

This aligns with the additive/group APIs and avoids bespoke finite-support machinery.

### 2) Rules

Paper: `F : D ⇒ X` (nonempty set-valued correspondence).

Lean representation:
- `RuleOn D X := {d // d ∈ D} → Set X`

This keeps domain membership explicit while preserving the paper’s set-valued semantics.

### 3) Reinforcement

The paper’s weak additivity and reinforcement are encoded directly over subtype-indexed rules.

### 4) Scoring and balance semantics

- Scoring: `arg max` over score totals.
- Balance: winner iff all pairwise balances are nonnegative.

Scoring/balance semantics are defined abstractly over general ordered additive codomains.

### 5) Quotient scaffolding for Theorem 1

The Theorem 1 proof requires quotient groups indexed by candidate pairs.
In this phase, we provide a reusable scaffold for pairwise quotient data and maps (`b^{x,y}`), without yet proving the full construction from reinforcement.

## Detailed Staged Plan

### Stage A (implemented now): abstract base layer
- Implement `Core.lean`, `Profiles.lean`, `Rules.lean`.
- Include:
  - domain/cone predicates,
  - `NProfile`/`ZProfile` aliases,
  - reinforcement definitions,
  - canonical profile embeddings and permutation helpers.

### Stage B (implemented now): scoring/balance semantics
- Implement `Scoring.lean`, `Balance.lean`.
- Include:
  - evaluation maps on finitely supported profiles,
  - `ScoreSystem`, `BalanceSystem`,
  - induced abstract voting correspondences,
  - linearity lemmas (`eval` over profile addition),
  - score-to-balance translation skeleton.

### Stage C (implemented now): Theorem 1 core scaffolding
- Implement `Theorem1/Cones.lean`,
  `Theorem1/PairwiseOrders.lean`, `Theorem1/Main.lean`.
- Include:
  - winner cones `C_x`,
  - proof that `C_x` is additively closed under reinforcement,
  - pairwise difference cone `P_{x,y}` in `ZProfile`,
  - induced relation from conoid form,
  - symmetric-kernel set placeholder,
  - quotient/pairwise-map scaffolding for `b^{x,y}`.

### Stage D (completed): Theorem 1 representation and corrected packaging layer
- Implemented in `Theorem1/Representation.lean`:
  - constructive direction `reinforcement -> balance representation` via
    `reinforcement_has_balance_representation`;
  - winner-cone preorder and canonical balance-system machinery;
  - converse direction under explicit structural assumptions via
    `balanceRule_reinforcement_of_perfect`, with hypotheses
    `WeaklyAdditive`, `BalanceSkew`, and `PerfectOn`.
- Implemented in `Theorem1/Packaging.lean`:
  - representability predicates:
    `IsBalanceRepresentable`,
    `IsPerfectBalanceRepresentable`,
    `IsPerfectSkewBalanceRepresentable`,
    `IsPerfectBalanceRuleRepresentable` (paper-facing synonym);
  - corrected Theorem 1 wrappers:
    `isBalanceRepresentable_of_reinforcement`,
    `reinforcement_of_perfectSkewBalanceRepresentation`,
    `reinforcement_of_perfectBalanceRepresentation`,
    `theorem1_corrected`,
    `theorem1_corrected_converse`,
    `theorem1_corrected_converse_paper`.
- Implemented in `Theorem1/LemmaC1.lean`:
  - full Lemma C.1 construction over an explicit codomain witness
    (`C1Codomain`) via pairwise quotient/linear-extension assembly;
  - theorem `lemmaC1`:
    `Reinforcement D F -> NonemptyOnDomain D F ->`
    `∃ B : BalanceSystem (C1Codomain ...) X V,`
    `PerfectOn B ∧ F = balanceRule B`.
  - paper-facing wrapper theorem
    `lemmaC1_reinforcement_to_isPerfectBalanceRepresentable`.
  - bridge packaging theorem `lemmaC1_representationBundle`:
    packages the same result as an explicit existential bundle over
    `(R, AddCommGroup R, LinearOrder R, B)`.
- Implemented in `Theorem1/OrderedAdditiveExtension.lean`:
  - `orderedAdditiveLinearOrder_of_cone`;
  - `homogeneous_szpilrajn_orderedAdditive` (homogeneous extension packaged
    with explicit ordered-additive/covariant instances).
- Implemented in `Theorem1/C1OrderedCodomain.lean`:
  - C.1 raw-codomain ordered machinery:
    `c1RawRel`, `c1RawRel_homogeneous`,
    `c1RawCodomain_orderedAdditive`;
  - saturation-based torsion/divisibility layer:
    pairwise cones are formalized via pure closure in
    `Theorem1/PairwiseOrders.lean`, yielding unconditional
    `pairwiseLinearQuotient_isAddTorsionFree`, then
    `c1PairCoord_isAddTorsionFree` and
    `c1RawCodomain_isAddTorsionFree`;
  - ordered-codomain bridge theorem:
    `lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable`
    (caller-facing skew bridge without explicit covariant-argument inputs,
    and now without extra divisibility/torsion assumptions in the theorem
    statement).

### Stage E (in progress): neutrality machinery
- Implemented:
  - generalized neutrality definitions for rules/score systems/balance systems
    via homomorphisms into permutation groups (`Neutrality/Defs.lean`);
  - Lemma C.2(a,b) with explicit permutation/evaluation statements
    (`Neutrality/LemmaC2.lean`).
  - Proposition 1 forward direction (`nu`-neutral score system implies
    `nu`-neutral induced scoring rule), in
    `Neutrality/Proposition1.lean`.
  - Proposition 1 converse via averaged score systems, with explicit
    nonemptiness assumption:
    core theorem
    `exists_scoreNeutral_of_ruleNeutral_scoringRule_with_nonempty`
    (`Neutrality/Proposition1.lean`).
  - Proposition 1 converse packaging refinements:
    automatic nonemptiness from finite/nonempty alternatives via
    `scoringRule_nonempty`/`scoringRule_nonemptyOnDomain`
    (`Scoring.lean`), and packaged converse
    `exists_scoreNeutral_of_ruleNeutral_scoringRule`
    (`Neutrality/Proposition1.lean`).
  - finite-group wrapper
    `exists_scoreNeutral_of_ruleNeutral_scoringRule_of_finiteGroup`
    so callers can assume `Finite G` instead of explicit `Fintype G`
    (`Neutrality/Proposition1.lean`).
  - Proposition 2 balance-side neutrality layer in
    `Neutrality/Proposition2.lean`:
    - forward direction
      `balanceRule_ruleNeutral_of_balanceNeutral`;
    - converse on explicit perfect/skew representations via averaged balance
      systems:
      `exists_balanceNeutralPerfectSkew_of_ruleNeutral_balanceRule_with_nonempty`;
    - packaging over explicit represented rules:
      `exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty`;
    - direct Stage-D-predicate wrapper:
      `exists_balanceNeutralPerfectSkewRepresentation_of_ruleNeutral`
      (from `IsPerfectBalanceRuleRepresentable`);
    - paper-facing wrapper alias:
      `exists_balanceNeutralPerfectRepresentation_of_ruleNeutral`;
    - packaged `iff` theorem under the Stage-D predicate interface:
      `proposition2_of_perfectSkewRepresentation`;
    - paper-facing packaged `iff` alias:
      `proposition2_of_perfectRepresentation`;
    - finite-group wrapper for the explicit-representation converse:
      `exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty_of_finiteGroup`.
- Remaining:
  - investigate whether the Proposition 1 converse can avoid
    `IsOrderedCancelAddMonoid R` (currently used through `Finset.sum_lt_sum`
    in the strict-inequality comparison step).

## Paper Correspondence Status (Objective)

- Theorem 1, forward:
  proved as `isBalanceRepresentable_of_reinforcement`
  (`Theorem1/Packaging.lean`), i.e.
  `Reinforcement D F -> IsBalanceRepresentable F`.
- Theorem 1, converse:
  proved as `reinforcement_of_perfectBalanceRepresentation`
  (`Theorem1/Packaging.lean`) under explicit assumptions
  `WeaklyAdditive D F` and `IsPerfectBalanceRuleRepresentable F`
  (`IsPerfectSkewBalanceRepresentable` remains as a compatibility synonym).
- Lemma C.1:
  formalized in `Theorem1/LemmaC1.lean`, including:
  - wrapper theorems for forward representability and Claim C.1.1 pairwise
    forms (`lemmaC1_reinforcement_to_isBalanceRepresentable`,
    `lemmaC1_forward`,
    `lemmaC1_claimC11a_pairwiseRel`, `lemmaC1_claimC11b_pairwiseRel`);
  - full constructive theorem `lemmaC1`:
    from reinforcement and explicit nonemptiness,
    constructs an explicit linearly ordered-codomain balance system with
    perfectness and exact rule equality.
  - paper-facing representability wrapper
    `lemmaC1_reinforcement_to_isPerfectBalanceRepresentable`.
  - bridge theorem `lemmaC1_representationBundle`:
    re-expresses this witness in explicit existential-bundle form.
  - ordered-codomain Stage-D skew bridge theorem (in
    `Theorem1/C1OrderedCodomain.lean`):
    `lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable`
    with no extra torsion-freeness assumption in its statement.
- Lemma C.2:
  fully formalized as `lemmaC2a_evalNat_permuteWeight` and
  `lemmaC2b_permuteWeight_comp` (`Neutrality/LemmaC2.lean`).
- Proposition 1:
  both directions are formalized in `Neutrality/Proposition1.lean`, with
  explicit assumptions (notably finite-group averaging and nonemptiness
  packaging where required).
- Lemma C.3:
  both directions are formalized in `Neutrality/Proposition2.lean`:
  `lemmaC3_left_of_balanceNeutral` and
  `lemmaC3_right_of_ruleNeutral_balanceRule_with_nonempty`
  (the right direction includes explicit perfect/skew and nonemptiness
  assumptions).
- Proposition 2 (paper statement):
  packaged as `proposition2_of_perfectRepresentation`
  (`Neutrality/Proposition2.lean`) under explicit assumptions:
  domain invariance, nonemptiness, and an input witness of
  `IsPerfectBalanceRuleRepresentable`
  (`proposition2_of_perfectSkewRepresentation` remains as a compatibility alias).
  Current bridge status:
  - resolved by saturation: pairwise kernels are replaced internally by their
    pure/divisible closure, giving unconditional pairwise quotient
    torsion-freeness and hence unconditional C.1 raw-codomain
    torsion-freeness for the ordered-codomain bridge.
  - note on correspondence: this is a faithful strengthening of the internal
    construction (same external theorem statements), with the quotient step
    routed through the saturated kernel.

### Stage F: Theorem 2
- C.4 equivalence (balance cocycle <-> scoring).
- C.5--C.7 divisibility/cone arguments.
- C.8 orbit-partition combinatorics.
- Main theorem.

### Stage G: bridge into `SocialChoice`
- Translate concrete `Profile`-based rules into count-profile semantics.
- Bridge existing reinforcement/scoring results.

## Milestones and Acceptance Criteria

1. **M1 (done in this phase)**: abstract layer files compile and expose stable APIs.
2. **M2 (done in this phase)**: scoring/balance semantics compile with key additivity lemmas.
3. **M3 (done in this phase)**: Theorem 1 core scaffolding compiles with winner-cone closure result.
4. **M4 (done in this phase)**: Stage-D Theorem 1 representation layer proved
   (constructive direction plus converse under explicit structural assumptions).
5. **M5**: Proposition 1 and 2 proved.
6. **M6**: full Theorem 2 proved.
7. **M7**: bridge file(s) connecting to `SocialChoice` abstractions.

## Risks and Mitigations

1. **Risk**: quotient/relation proof obligations become brittle.
   - Mitigation: isolate reusable quotient scaffolds and relation builders early.

2. **Risk**: Section C.8 combinatorics dominates implementation time.
   - Mitigation: stage C.8 into orbit partition lemmas + equation-packaging lemmas before final synthesis.

3. **Risk**: mismatch between abstract `Set`-valued rules and existing `Finset`-valued rules.
   - Mitigation: defer bridge until abstract layer is stable; keep bridge thin and explicit.

## Conventions for Future Work

- Keep theorem names close to paper references where possible (`lemmaC1_*`, `proposition1_*`, etc.).
- Prefer short helper lemmas around profile addition and permutation actions before larger proofs.
- Keep files small and thematic to avoid monolithic Appendix C files.
- Use existing Appendix B lemmas directly rather than duplicating order/conoid infrastructure.
