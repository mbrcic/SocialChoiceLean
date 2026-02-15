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

Status: in progress (paper-facing interfaces are now exact-paper shape; remaining work is internal C.8 bridge proof completion).

Implemented and compiling:
- Generic Theorem-2 assembly wrappers in `Theorem2/Main.lean`:
  - `theorem2_forward`
  - `theorem2_backward`
  - `theorem2`
- Paper-facing wrappers (`mu = id` on `Perm X`) in `Theorem2/Main.lean`:
  - `theorem2_forward_paper`
  - `theorem2_paper`
  - explicit C.8 cycle packaging assumptions removed from signatures.
- C.8 packaging interface cleanup:
  - `C8CycleSumHypothesis` introduced in `Theorem2/C8Seed.lean`
  - branch split represented through named C.8.3 / C.8.4 branch predicates.
- New groundwork file:
  - `Theorem2/C8Branch.lean` (orbit/transport helper lemmas for C.8 branch derivation).
  - includes a proved hull-selection bridge:
    `exists_orbitSet_hull_eq_of_neutral_balance`
    (Claim C.8.1 + Claim C.8.2 + Lemma C.7 assembly).
  - includes a proved three-cycle branch theorem:
    `cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq`.
- New orbit-layer wrapper:
  - `lemmaC8_of_neutral_perfect_balance_threeCycleHullEq` in
    `Theorem2/C8Orbit.lean` (derives Eq. (C.21) from the three-cycle hull branch, then applies paper-facing C.8 wrapper).
- New bridge assembly file:
  - `Theorem2/C8Bridge.lean` introduces
    `c8CycleSumHypothesis_of_neutral_perfect_balance_paper`.
  - `Theorem2/C8Orbit.lean` and `Theorem2/Main.lean` now route paper-facing wrappers through this bridge so no explicit `hCycle` argument remains.
- New fallback staging file:
  - `Theorem2/C8Fallback.lean` holds the C.8.4 path in decomposed form.
  - Step-3 bridge cases in `Theorem2/C8Bridge.lean` now call this module, so fallback work is isolated and reviewable.

Current C.8 bridge decomposition (implemented):
1. `C8Bridge`:
   - small-card cocycle (`|X| ≤ 2`) helper;
   - reinforcement derivation from cone + skew + perfectness;
   - `% 3` dispatcher and paper-facing bridge wrapper.
2. `C8Fallback`:
   - C.8.4 equation-pack layer;
   - conversion from equation-pack to four/five-cycle branch hypothesis;
   - case-1 and case-2 packaging entry points.
3. `C8Orbit` / `Main`:
   - paper-facing Lemma C.8 and Theorem 2 wrappers consume bridge output directly;
   - explicit cycle hypothesis removed from paper-facing signatures.

Current remaining gap:
- Internal placeholders remain in the bridge pipeline:
  - `Theorem2/C8Bridge.lean`:
    - `c8Bridge_step2_threeCycleBranch_of_case0`
  - `Theorem2/C8Fallback.lean`:
    - generation of fallback equation packs in `% 3 = 1` and `% 3 = 2`.
- This is the technical blocker for closing Stage F with no placeholders.

Tasks:
1. Complete `% 3 = 0` bridge path:
   - prove `c8Bridge_step2_threeCycleBranch_of_case0`.
2. Complete C.8.4 case generation:
   - prove `% 3 = 1` and `% 3 = 2` equation-pack generation lemmas in `C8Fallback`.
3. Remove all remaining `sorry` in `Theorem2/C8Bridge.lean` and `Theorem2/C8Fallback.lean` while preserving current public theorem signatures.
4. Keep generic theorem wrappers as reusable infrastructure.

Exit criterion:
- Paper-facing Theorem 2 wrapper in `Theorem2/Main.lean` remains free of
  explicit C.8 cycle/branch/seed/transport assumptions, and the bridge theorem
  pipeline (`Theorem2/C8Bridge.lean` + `Theorem2/C8Fallback.lean`) is fully
  proved (no placeholders), while keeping explicit `hInv` per current interface
  decision.

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
