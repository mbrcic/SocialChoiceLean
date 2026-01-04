# Translation Guide: Universe Polymorphism Removal

## Goal

Convert the codebase from universe-polymorphic types (`Type*`) to universe-monomorphic types (`Type`). This fixes issues with negative results (counterexamples, impossibility theorems) where Lean cannot unify polymorphic universe variables with concrete types.

## Background

- `Type*` means `Type u` for an implicit universe variable `u` — it ranges over all universes
- `Type` (without `*`) means `Type 0` — the base universe containing `Nat`, `Fin n`, `Bool`, etc.
- All finite types used in this project (voters, candidates) live in `Type 0`

---

## Translation Rules

### Rule 1: Type Declarations

**Find:** `{V A : Type*}` or `(V A : Type*)`  
**Replace with:** `{V A : Type}` or `(V A : Type}`

**Examples:**
```lean
-- Before:
def Prefers {V A : Type*} [Fintype V] [Fintype A] ...

-- After:
def Prefers {V A : Type} [Fintype V] [Fintype A] ...
```

```lean
-- Before:
structure Profile (V A : Type*) [Fintype V] [Fintype A] where

-- After:
structure Profile (V A : Type) [Fintype V] [Fintype A] where
```

### Rule 2: Single Type Variables

**Find:** `{A : Type*}` or `(A : Type*)`  
**Replace with:** `{A : Type}` or `(A : Type)`

**Examples:**
```lean
-- Before:
def BallotTop {A : Type*} (r : LinearOrder A) (c : A) : Prop :=

-- After:  
def BallotTop {A : Type} (r : LinearOrder A) (c : A) : Prop :=
```

### Rule 3: Three or More Type Variables

**Find:** `{V W A : Type*}` or similar patterns  
**Replace with:** `{V W A : Type}`

**Examples:**
```lean
-- Before:
def unionProfiles {V W A : Type*} [Fintype V] [Fintype W] [Fintype A] ...

-- After:
def unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A] ...
```

### Rule 4: Explicit Universe Annotations

**Find:** `VotingRule.{0, 0}` or similar explicit universe pinning  
**Replace with:** `VotingRule` (no annotation needed)

**Explanation:** After the translation, `VotingRule` is already at universe 0, so explicit annotations are redundant.

**Examples:**
```lean
-- Before:
theorem no_resolute_condorcet_strategyproof_3x3
    (f : VotingRule.{0, 0}) (hf : Resolute f) : ...

-- After:
theorem no_resolute_condorcet_strategyproof_3x3
    (f : VotingRule) (hf : Resolute f) : ...
```

### Rule 5: Greek Letter Type Variables

Some files may use `{α : Type*}` or `{β : Type*}`.

**Find:** `{α : Type*}` or `(α : Type*)`  
**Replace with:** `{α : Type}` or `(α : Type)`

---

## Files to Modify

The following files should be checked for `Type*` patterns:

### Core Files (Start Here)
1. `SocialChoice/Profile.lean` — Core definitions of `Profile`, `VotingRule`, etc.
2. `SocialChoice/Rules.lean` — Additional rule definitions

### Axiom Files
3. `SocialChoice/Axioms/*.lean` — All files in the Axioms directory

### Rule Files  
4. `SocialChoice/Rules/**/*.lean` — All files in the Rules directory (recursive)

### Impossibility Files
5. `SocialChoice/Impossibilities/*.lean` — May have explicit `.{0, 0}` annotations to remove

### Example/Helper Files
6. `SocialChoice/Examples.lean` — If it exists
7. Any other `.lean` files in the `SocialChoice/` directory

---

## Verification Steps

After making changes, verify:

1. **Build succeeds:** Run `lake build` from the project root
2. **No universe errors:** Check that files like `SocialChoice/Rules/ScoringRules/Borda/Majority.lean` now compile without the `Type mismatch ... Eq.{u_2 + 1} ... Eq.{1}` errors
3. **Existing proofs still work:** Positive results (e.g., "Borda satisfies Anonymity") should continue to compile

---

### Rule 6: Universe Declarations

**Find:** `universe u v` or `universe u` at the top of files  
**Action:** Remove the entire line

**Explanation:** These declarations were workarounds for universe polymorphism. With `Type` (universe 0), they are no longer needed and should be removed to keep the code clean.

**Examples:**
```lean
-- Before:
import Mathlib.Data.Fintype.Basic
universe u v

namespace SocialChoice
...

-- After:
import Mathlib.Data.Fintype.Basic

namespace SocialChoice
...
```

---

## What NOT to Change

1. **Mathlib imports** — Do not modify anything in mathlib; only modify project files
2. **`Prop` or `Sort*`** — Only change `Type*`, not other sort annotations

---

## Common Patterns Quick Reference

| Before | After |
|--------|-------|
| `{V A : Type*}` | `{V A : Type}` |
| `(V A : Type*)` | `(V A : Type)` |
| `{A : Type*}` | `{A : Type}` |
| `{V W A : Type*}` | `{V W A : Type}` |
| `{α : Type*}` | `{α : Type}` |
| `VotingRule.{0, 0}` | `VotingRule` |
| `Profile.{0, 0}` | `Profile` |

---

## Troubleshooting

If after the translation you encounter errors:

1. **"unknown universe level"** — Check for leftover `.{0, 0}` annotations or `universe` declarations that reference unused variables

2. **"type mismatch" with universes** — You may have missed a `Type*` somewhere; search the file for `Type*`

3. **Mathlib lemma application fails** — Some mathlib lemmas are universe-polymorphic; you may need to provide explicit type annotations to help Lean infer the right universe. Example:
   ```lean
   -- If this fails:
   exact some_mathlib_lemma h
   
   -- Try:
   exact @some_mathlib_lemma (V := V) (A := A) h
   ```

4. **"failed to synthesize instance"** — Make sure `[Fintype V]` and `[Fintype A]` instances are still present after the type change
