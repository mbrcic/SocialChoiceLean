# Pivato Formalization Plan

Last updated: February 14, 2026.

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
- Final C.8 branch-packaging theorem removing explicit `hBranch` from the paper-facing Theorem 2 wrapper.
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

Status: in progress (core wrappers proved; one C.8 bridge gap remains).

Implemented and compiling:
- Generic Theorem-2 assembly wrappers in `Theorem2/Main.lean`:
  - `theorem2_forward`
  - `theorem2_backward`
  - `theorem2`
- Paper-facing wrappers (`mu = id` on `Perm X`) in `Theorem2/Main.lean`:
  - `theorem2_forward_paper`
  - `theorem2_paper`
  - explicit `hSeed`/`hTransport` removed from paper-facing signatures.
- C.8 packaging interface cleanup:
  - `C8CycleSumHypothesis` introduced in `Theorem2/C8Seed.lean`
  - branch split represented as an internal disjunction over `C8CycleSumHypothesis`
  - paper-facing wrappers now consume cycle-sum packaging directly.
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

Current remaining gap:
- `theorem2_paper` still requires explicit cycle-sum packaging input
  `hCycle : ... → C8CycleSumHypothesis ...` in full generality.
- What is now covered:
  - the C.8.1/C.8.2/Lemma-C.7 hull-selection step is formalized.
  - the C.8.3-style three-cycle branch is formalized as a reusable theorem.
- What is still missing for full paper packaging:
  - case-level assembly guaranteeing that one of the required branches applies
    from only the paper assumptions (not yet reduced to a single wrapper theorem);
  - C.8.4 four/five-cycle fallback packaging as an internal theorem feeding
    `C8CycleSumHypothesis`;
  - final elimination of explicit `hCycle` from `theorem2_forward_paper` / `theorem2_paper`.

Tasks:
1. Prove the missing C.8 branch-packaging theorem:
   from cone + neutrality + perfect representation assumptions, derive
   `C8CycleSumHypothesis` (equivalently, `C8BranchSplitHypothesis`).
2. Use (1) to produce an exact paper-facing Theorem 2 wrapper with explicit
   `hInv` but without explicit C.8 cycle/branch/seed/transport assumptions.
3. Keep generic theorem wrappers as infrastructure for future reuse.

Exit criterion:
- A paper-facing theorem in `Theorem2/Main.lean` matching Theorem 2 with no
  explicit C.8 cycle/branch/seed/transport assumptions (while keeping explicit `hInv`
  per current interface decision).

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
