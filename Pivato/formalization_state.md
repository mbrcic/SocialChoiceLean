# Pivato Formalization Plan

Last updated: February 17, 2026.

## Purpose

This document tracks the formalization roadmap for `Pivato/` at the theorem level.
It is intentionally implementation-light: we record what is proved, what is not yet proved, and the next milestones.

## Current Repository Status

Implemented and compiling:
- Core abstractions: `Core.lean`, `Profiles.lean`, `Rules.lean`
- Scoring and balance semantics: `Scoring.lean`, `Balance.lean`
- Appendix B machinery: `HomogeneousSzpilrajn.lean`, `AppendixB.lean`
- Theorem 1 development:
  - `Theorem1/Cones.lean`
  - `Theorem1/PairwiseOrders.lean`
  - `Theorem1/Representation.lean`
  - `Theorem1/Packaging.lean`
  - `Theorem1/LemmaC1.lean`
  - `Theorem1/OrderedAdditiveExtension.lean`
  - `Theorem1/Skewification.lean`
  - `Theorem1/C1OrderedCodomain.lean`
  - `Theorem1/Main.lean`
- Neutrality layer:
  - `Neutrality/Defs.lean`
  - `Neutrality/LemmaC2.lean`
  - `Neutrality/Proposition1.lean`
  - `Neutrality/Proposition2.lean`
  - `Neutrality/Main.lean`

Not started yet:
- `Bridge/*` files into `SocialChoice`

## Objective Paper-Correspondence Status

Theorem-level status:
- Theorem 1 (forward direction): formalized.
  - Reinforcement implies balance representability.
- Theorem 1 (converse direction): formalized in corrected explicit form.
  - Uses explicit structural assumptions (`WeaklyAdditive`, perfectness, skewness).
- Lemma C.1: formalized as a constructive representation result.
  - Internal quotient step uses saturated/pure closure of the pairwise kernel so torsion-freeness is available unconditionally.
  - External theorem intent is preserved (representation construction with perfectness).
- Lemma C.2: formalized.
- Proposition 1: formalized (both directions) with explicit finite-group/nonemptiness assumptions where needed.
- Proposition 2: formalized in packaged form under explicit representation assumptions.

Still missing for full paper coverage:
- Internal no-placeholder completion of the C.8 bridge core:
  - case `% 3 = 0` assembly (C.8.1/C.8.2/C.8.3 path),
  - case `% 3 = 1,2` fallback packaging/conversion (C.8.4 path),
  - final elimination of remaining `sorry` in C.8 bridge internals.
- Bridge from abstract Pivato layer to concrete `SocialChoice` rules.

## Modeling Decisions (Current)

Profiles/domains:
- `NProfile V := V →₀ ℕ`
- `ZProfile V := V →₀ ℤ`
- `Domain V := Set (NProfile V)`

Rules:
- `RuleOn D X := {d // d ∈ D} → Set X`

Nonemptiness:
- Tracked explicitly via hypotheses such as `NonemptyOnDomain D F`.
- This keeps theorem statements honest about where nonemptiness is used.

Pairwise quotient step:
- Uses saturated (pure/divisible) closure internally in the C.1 pipeline.
- Purpose: ensure quotient torsion-freeness needed for ordered additive extension without extra global assumptions.

## Deferred Design Decision: `RuleOn` vs bundled `VotingRuleOn`

Decision (for now): keep `RuleOn` unchanged.

Reason:
- Changing `RuleOn` to enforce nonemptiness globally would force a broad refactor across existing files and proof interfaces.
- Current development already separates core rule semantics from extra assumptions cleanly.

Deferred option:
- Introduce a bundled wrapper (for example `VotingRuleOn`) that packages:
  - a `RuleOn D X`,
  - nonemptiness on domain,
  - optionally other paper-side side conditions.
- This can be done after Theorem 2 so we do not block theorem progress on interface churn.

## Concrete Staged Plan

### Stage E (neutrality layer): finalize and stabilize

Status: completed.

Completed deliverables:
1. Proposition 1 forward/converse formalized, plus packaged `iff` wrappers:
   - `proposition1_of_scoringRepresentation_with_nonempty`
   - `proposition1_of_scoringRepresentation`
2. Proposition 2 forward/converse and packaged `iff` formalized.
3. Neutrality API consolidated in `Neutrality/Main.lean` with stable exported theorem names.
4. Internal assumptions are explicit in theorem statements; no unresolved linter diagnostics in neutrality files.

Exit criterion: satisfied.

### Stage F (Theorem 2): main technical milestone

Status: in progress.

Build reality check (February 17, 2026):
- `lake build Pivato.Theorem2.Main` succeeds.
- Remaining `sorry` declarations in Stage F:
  - `Theorem2/C8Branch.lean`:
    - `cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq`
  - `Theorem2/C8Fallback.lean`:
    - `c8EqC21_designated_of_equationPack4`
    - `c8EqC21_designated_of_equationPack5`
    - `c8Fallback_case1_exists_hullWitness`
    - `c8Fallback_case2_exists_hullWitness`
    - `c8Fallback_case1_classify_witnessOrbit`
    - `c8Fallback_case2_classify_witnessOrbit`
    - `c8Fallback_case1_cycleSum_of_threeOrbitWitness`
    - `c8Fallback_case2_cycleSum_of_threeOrbitWitness`
    - `c8Fallback_case1_equationPack4_of_bigOrbitWitness`
    - `c8Fallback_case2_equationPack5_of_bigOrbitWitness`

What is done:
- Paper-facing wrappers compile:
  - `theorem2_forward_paper`, `theorem2_paper` in `Theorem2/Main.lean`
  - `lemmaC8_of_representation_paper` in `Theorem2/C8Orbit.lean`
- C.8 branch interfaces are explicit:
  - `C8ThreeCycleBranchHypothesis` (C.8.3 payload)
  - `C8FourFiveCycleBranchHypothesis` with separate constructors
    `ofFourCycle` and `ofFiveCycle` (C.8.4 payload)
- Case `% 3 = 1,2` route now produces a true branch split (`Or.inl` or `Or.inr`)
  from witness classification in `Theorem2/C8Fallback.lean`.
- Fallback equation packs use paper-form equations:
  - Case 1: `(C.9)--(C.14)`
  - Case 2: `(C.15)--(C.20)`
- Designated-point packaging lemmas are in place:
  - `c8Fallback_fourFiveCycleBranch_of_equationPack4`
  - `c8Fallback_fourFiveCycleBranch_of_equationPack5`
- Case `% 3 = 0` bridge theorem is implemented:
  - `c8Bridge_step2_threeCycleBranch_of_case0`

Current Stage F structure (by file):
- `Theorem2/C8Seed.lean`: branch hypotheses and branch-split/seed conversion.
- `Theorem2/C8Branch.lean`: orbit/hull infrastructure and generalized period-`M`
  three-cycle core (`3 ∣ M+1`).
- `Theorem2/C8OrbitCases.lean`: combinatorial case data for `% 3 = 0/1/2`,
  including Case 1/2 period data (`12/15` in mixed-orbit regimes).
- `Theorem2/C8Fallback.lean`: C.8.4 equation packs, designated Eq. (C.21)
  reductions, and case-1/case-2 branch-split assembly.
- `Theorem2/C8Bridge.lean`: cardinality case split and C.8 branch assembly.
- `Theorem2/C8Orbit.lean`: conversion from C.8 seed to scoring representation.

Remaining tasks (critical path):
1. Prove `cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq`
   (`Theorem2/C8Branch.lean`) in full period-`M` form.
2. Prove designated Eq. (C.21) reductions from paper equation packs:
   - `c8EqC21_designated_of_equationPack4`
   - `c8EqC21_designated_of_equationPack5`
3. Complete fallback witness pipeline in `Theorem2/C8Fallback.lean`:
   existence, orbit classification, three-orbit C.8.3 route, and big-orbit
   C.8.4 equation-pack construction.
4. Remove all Stage F `sorry` declarations and keep `theorem2_paper` compiling.

Exit criterion:
- `theorem2_paper` remains paper-facing (no explicit seed/transport/cycle
  assumptions), and all Stage F internals are sorry-free.

### Stage G (bridge to `SocialChoice`)

Status: not started.

Tasks:
1. Define translation layer from concrete profile/rule interfaces to `Pivato` abstract interfaces.
2. Prove bridge lemmas for reinforcement/scoring assumptions needed by imported theorems.
3. Demonstrate at least one end-to-end application of Theorem 2 machinery to an existing `SocialChoice` artifact.

Exit criterion:
- At least one concrete rule/axiom result in `SocialChoice` can be obtained through the new bridge.

## Milestones

Completed:
1. M1: abstract base layer
2. M2: scoring/balance semantics
3. M3: Theorem 1 cone/quotient scaffolding
4. M4: Theorem 1 + Lemma C.1 pipeline
5. M5: neutrality layer stabilization for Theorem 2 inputs

Upcoming:
6. M6: full Theorem 2 formalization
7. M7: bridge to `SocialChoice`

## Working Convention for This Plan

When updating this file:
- Prefer theorem-level status over sublemma inventories.
- Record only decisions that affect interfaces or proof strategy.
- Keep temporary implementation details in code comments or PR notes, not in this roadmap.
