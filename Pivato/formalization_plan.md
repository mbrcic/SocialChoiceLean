# Pivato Formalization Plan

Last updated: February 15, 2026.

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

Build reality check (February 15, 2026):
- `lake build Pivato` succeeds.
- Exactly three declarations still use `sorry`:
  - `Theorem2/C8Bridge.lean`: `c8Bridge_step2_threeCycleBranch_of_case0`
  - `Theorem2/C8Fallback.lean`: `c8Fallback_equationPack45_of_case1`
  - `Theorem2/C8Fallback.lean`: `c8Fallback_equationPack45_of_case2`

What is already done:
- Paper-facing wrappers are in place and compile:
  - `theorem2_forward_paper`, `theorem2_paper` in `Theorem2/Main.lean`
  - `lemmaC8_of_representation_paper` in `Theorem2/C8Orbit.lean`
- The C.8 pipeline has substantial completed infrastructure:
  - orbit/block/hull assembly in `C8Branch.lean`
  - `% 3` combinatorial orbit data in `C8OrbitCases.lean`
  - transport and Claim C.8.5 packaging in `C8Transport.lean` and `C8Claim5.lean`
  - fallback equation-derivation helpers in `C8Fallback.lean`

Important caveat about paper correspondence:
- The main paper-facing theorem exists (`theorem2_paper`), but still depends on
  the three unfinished internals above. Stage F is therefore not complete.

Current blocker analysis:
1. Case `% 3 = 0` bridge (`C8Bridge`):
   - The remaining hole is a local derivation of
     `NonemptyOnDomain D (balanceRule (D := D) B)` inside
     `c8Bridge_step2_threeCycleBranch_of_case0`.
   - This is a design pressure point: if the derivation is not available from
     current hypotheses, we should pass this assumption explicitly at bridge
     level and thread it consistently.
2. Cases `% 3 = 1,2` fallback (`C8Fallback`):
   - Remaining atomic equations:
     - case 1: `C10`
     - case 2: `C16`, `C15`
   - Everything else in the fallback equation-pack assembly is largely in place.

Known source of confusion (to clean up after proofs close):
- In `C8Seed.lean`, `C8ThreeCycleBranchHypothesis` and
  `C8FourFiveCycleBranchHypothesis` are currently aliases of the same
  `C8CycleSumHypothesis`, so `C8BranchSplitHypothesis` is propositionally
  equivalent to a single hypothesis.
- This is acceptable as temporary packaging, but it obscures whether we have
  truly formalized distinct C.8.3 vs C.8.4 reasoning.

Likely temporary/dead code to review for deletion after Stage F closes:
- `Theorem2/C8Orbit.lean`:
  - `lemmaC8_of_neutral_perfect_balance_threeCycleHullEq`
- `Theorem2/C8Fallback.lean`:
  - `c8Fallback_equationPack4_of_cycleSum`
  - `c8Fallback_cycleSumHypothesis_of_case1`
- `Theorem2/C8OrbitCases.lean`:
  - point-pattern/fallback wrapper scaffolding not referenced by bridge output
    (`C8FallbackPointPattern4/5`, `C8FallbackOrbitCase` and related wrappers),
    unless they become part of the final fallback proof route.

Policy for cleanup:
- Do not delete these while the three `sorry` remain.
- After placeholders are removed and signatures stabilize, run one dedicated
  cleanup pass:
  - delete unused wrappers/scaffolding,
  - simplify branch naming to match actual proof structure,
  - keep only declarations used by `theorem2_paper`.

Remaining tasks (critical path):
1. Finish `c8Bridge_step2_threeCycleBranch_of_case0` (`C8Bridge.lean`).
2. Finish `c8Fallback_equationPack45_of_case1` and
   `c8Fallback_equationPack45_of_case2` (`C8Fallback.lean`).
3. Remove all `sorry` from `Theorem2/C8Bridge.lean` and
   `Theorem2/C8Fallback.lean`.
4. Run cleanup pass for likely temporary/dead declarations after step 3.

Exit criterion:
- `theorem2_paper` remains paper-facing (no explicit seed/transport/cycle
  assumptions), C.8 internals are sorry-free, and temporary scaffolding is
  trimmed so the proof route is auditable.

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
