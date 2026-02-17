# Plan: Rewrite Lemma C.8 (Paper-Faithful, Clean-Slate)

## Background

We are formalizing Pivato's characterization theorem for scoring rules (`Pivato/pivato.tex`).  
Lemma C.8 is the central technical step: prove the cocycle identity

`b(x,y,d) + b(y,z,d) = b(x,z,d)`

for all pairwise distinct `x y z` and all `d ∈ D`, under neutrality + reinforcement assumptions.

The paper's structure is:
1. Partition `X` into one big block `X₀` (size 4 in Case 1, size 5 in Case 2) and remaining 3-blocks.
2. Build a permutation `φ` whose orbits are exactly those blocks (no fixed points).
3. Define orbit-sum profiles and orbit-block domains.
4. Apply Lemma C.7 (hull selection): pick one block whose hull equals hull of `D`.
5. If selected block is a 3-block, use Claim C.8.3 directly.
6. If selected block is the big block, use Claim C.8.4-style cycle-equation algebra.

## Design Principles (Explicit)

1. **Clean-slate first**: remove dead/obsolete C.8 fallback scaffolding early so readers only see the intended proof path.
2. **Correct assumptions from the start**: introduce `hNE : NonemptyOnDomain D (balanceRule ...)` at the top-level bridge and thread it immediately; no local placeholder derivations.
3. **Paper-faithful witness handling**: do not force `x0 = designatedPoint`; transport along orbit equality (`orbitSet φ x0 = orbitSet φ xBig`) and carry hull/block-domain facts across that identification.
4. **Generalize exactly where mathematically uniform**:
   - yes: telescoping/orbit-sum identity (`p ∣ T`);
   - no: keep 4-cycle and 5-cycle downstream equation algebra as separate case modules.

## Root Issues To Fix

1. Missing explicit nonemptiness hypothesis for `balanceRule` on `D`.
2. Wrong fallback permutation shape (`k`-cycle + identity tail) causing fixed points.
3. Hardcoded orbit lengths (`M=3`/`M=4`) where paper needs arbitrary `T` divisible by cycle length.
4. Incomplete 5-cycle hull-lift pipeline (Case 2).

## Step 0: Delete Obsolete C.8 Fallback Code

Delete declarations that are no longer part of the intended pipeline, including:
- `c8Fallback_eqC10_on_cycle4_blockDomain`
- `c8Fallback_eqC16_on_cycle5_blockDomain`
- `c8FallbackC10Hom_zero_on_cycle4_blockDomain`
- old fallback scaffolding (`C8FallbackPointPattern4/5`, `C8FallbackOrbitCase`) if not used in the rewritten proof
- old orbit-data constructors that rely on identity tails

Target files:
- `Pivato/Theorem2/C8Fallback.lean`
- `Pivato/Theorem2/C8OrbitCases.lean`

## Step 1: Thread `NonemptyOnDomain` From the Top

Add

`(hNE : NonemptyOnDomain D (balanceRule (D := D) B))`

as an explicit parameter to bridge/fallback entry points and upstream callers.

Minimum surface:
- `c8Bridge_step2_threeCycleBranch_of_case0`
- `c8Bridge_step4_branchSplit_of_neutral_perfect_balance_paper`
- `c8CycleSumHypothesis_of_neutral_perfect_balance_paper`
- `c8Fallback_equationPack45_of_case1`
- `c8Fallback_equationPack45_of_case2`
- relevant call chain in `C8Orbit.lean` and `Theorem2/Main.lean`

No local `have hNE := by sorry` is allowed after this step.

## Step 2: Rebuild Orbit Construction to Match Paper

Replace current Case 1/2 fallback permutation constructors with fixed-point-free orbit-partition constructors:

- Case 1 (`|X| % 3 = 1`): `φ = (product of 3-cycles) × (4-cycle)`
  - order `4` if no 3-block tail
  - order `12` otherwise
- Case 2 (`|X| % 3 = 2`): `φ = (product of 3-cycles) × (5-cycle)`
  - order `5` if no 3-block tail
  - order `15` otherwise

Required outputs:
- `φ^(T) = 1` for chosen period `T`
- `∀ x, φ x ≠ x`
- orbit classification theorem: each orbit is either a 3-orbit or the unique big orbit

Target file:
- `Pivato/Theorem2/C8OrbitCases.lean`

## Step 3: Add General Telescoping Lemma (Uniform Core)

Prove a generic orbit-sum decomposition for a `p`-cycle pair:

`∑_{k=0}^{T-1} B(φ^{-k}(a), φ^{-k}(b), d) = (T / p) • ψ(d)` when `p ∣ T`.

Use this to generalize:
- three-cycle branch lemma currently fixed at `M = 2`
- big-cycle block-domain sum lemmas currently fixed at 4/5 terms

Interpretation:
- for Case 1 big orbit: `p = 4`, `T = 4` or `12`
- for Case 2 big orbit: `p = 5`, `T = 5` or `15`
- for 3-orbits in all cases: `p = 3`, `T` divisible by `3`

Target files:
- `Pivato/Theorem2/C8Branch.lean`
- `Pivato/Theorem2/C8Fallback.lean`

## Step 4: Paper-Faithful C.7 Branch Split (No Point Equality Hack)

After C.7 gives witness `x0` with hull equality on `D_{x0}`:

1. Determine orbit type of `x0` (3-orbit or big orbit).
2. If 3-orbit: apply generalized C.8.3 branch directly to obtain cocycle.
3. If big orbit:
   - prove `orbitSet φ x0 = orbitSet φ xBig` for designated big-orbit point `xBig`;
   - transport block-domain and hull statements across this orbit equality;
   - lift big-cycle sum equation from block domain to `D`;
   - run existing 4-cycle or 5-cycle algebra (rotations/swaps) to derive cocycle.

This follows the paper exactly: the witness is a block representative, not a privileged named point.

Target files:
- `Pivato/Theorem2/C8Bridge.lean`
- `Pivato/Theorem2/C8Fallback.lean`

## Step 5: Complete Case 2 Hull-Lift Infrastructure

Mirror Case 1's hull-lift path for 5-cycles:
- block-domain 5-term equation (`C.15` style),
- hull-lift to `D`,
- derive `C.16`–`C.20` via rotation/combination,
- conclude cocycle.

Target file:
- `Pivato/Theorem2/C8Fallback.lean`

## Step 6: Assembly and Final Interface

Reassemble bridge theorem pipeline so the final C.8 output only depends on:
- cone/domain assumptions,
- skew/perfect/neutral/reinforcement assumptions,
- explicit `hNE`,
- cardinality split.

Target files:
- `Pivato/Theorem2/C8Bridge.lean`
- `Pivato/Theorem2/C8Orbit.lean`
- `Pivato/Theorem2/Main.lean`

## Implementation Method

Use sorry-driven decomposition, but only after Steps 0-2 are in place:
1. Declare full final lemma skeletons with `sorry`.
2. Ensure top-level theorem statement paths are correct.
3. Fill sorries in dependency order (generic telescoping first, then branch-specific algebra).
4. Update `formalization_state.md` incrementally.

## Checkpoints

1. **After Step 1**: no local synthetic derivations of `hNE`.
2. **After Step 2**: no fixed points in fallback `φ`; orbit classification theorem present.
3. **After Step 3**: no hardcoded orbit-length assumptions in core cycle-sum lemmas.
4. **After Step 4**: no proof step requiring `x0 = designatedPoint`.
5. **After Step 5**: Case 2 has a full hull-lift pipeline analogous to Case 1.
6. **Done**: `theorem2_paper` compiles through the rewritten C.8 pipeline (modulo any intentionally remaining sorries during staged development).

## Files Expected to Change

- `Pivato/Theorem2/C8OrbitCases.lean`
- `Pivato/Theorem2/C8Branch.lean`
- `Pivato/Theorem2/C8Fallback.lean`
- `Pivato/Theorem2/C8Bridge.lean`
- `Pivato/Theorem2/C8Orbit.lean`
- `Pivato/Theorem2/Main.lean`
