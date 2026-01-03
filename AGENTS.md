## Project Overview

`SocialChoiceLean` is a formalization of social choice theory using the **Lean 4** proof assistant. It leverages **mathlib4** to provide a rigorous framework for studying voting rules, preference profiles, and social choice axioms.

The project includes:
- **Core Abstractions:** Definitions for `Profile`, `VotingRule`, and preference relations.
- **Voting Rules:** Implementations of various rules including Scoring Rules (Borda, Plurality, Veto) and SplitCycle.
- **Axioms:** Formal definitions of properties like Anonymity, Neutrality, Condorcet consistency, Pareto efficiency, and Monotonicity.
- **Proofs:** Formal verification that specific rules satisfy certain axioms, and proofs of impossibility theorems (e.g., Condorcet Strategyproofness).

### Key Technologies
- **Lean 4:** The primary language and theorem prover.
- **Lake:** The build system and package manager for Lean 4.
- **mathlib4:** The standard mathematical library for Lean 4.

## Project Structure

- `SocialChoice/`: The main library directory.
    - `Basic.lean` / `Profile.lean`: Fundamental definitions for preference profiles and voting rules.
    - `Axioms/`: Formal definitions of social choice properties.
    - `Rules/`: Specific voting rule implementations and their properties.
        - `ScoringRules/`: Borda, Plurality, Veto, etc.
        - `SplitCycle/`: Implementation and properties of the SplitCycle rule.
    - `Impossibilities/`: Formalized impossibility results.
- `Main.lean`: The executable entry point.
- `lakefile.toml`: Configuration for the Lake build system.
- `lean-toolchain`: Specifies the Lean 4 version used (currently `v4.27.0-rc1`).

### Testing
No testing is required as the project focuses on formal proofs. Verification is done through Lean's type checker.

## Development Conventions

- **Naming:** Follows Lean 4 and mathlib conventions (CamelCase for types, snake_case for definitions and theorems).
- **Axioms:** Axioms are typically defined as predicates on `VotingRule` (e.g., `def Anonymity (f : VotingRule) : Prop`).
- **Mathematical Style:** Uses `Fintype` for finite sets of voters and candidates, and `Finset` for result sets.
- **Modularity:** New rules should be added to `SocialChoice/Rules/`, and their axioms to `SocialChoice/Axioms/`.

## Using lean-lsp

The user prefers that agents read files directly from the file system using their dedicated file read tool. For long files, it can be judicious to read them in chunks. Avoid using the `lean_file_contents` tool since its output is less readable.

For most other tasks, the user prefers that agents use tools provided by the lean-lsp mcp plugin.

### Searching mathlib4

When searching for definitions, the user prefers that agents use the `lean_loogle`, `lean_leansearch`, and `lean_leanfinder` tools provided by the lean-lsp mcp plugin. These tools should be used liberally as they can speed up exploration significantly. There are rate limits of several requests per 30 seconds. Given how agents are implemented, this means that for *every* turn, these rate limits will be available, so can be used. (e.g. if the user entered a message, this will have taken >30s so the rate limits will have reset; if the agent requested diagnostics, this also takes sufficient time to reset limits).

Note: these tools only search mathlib4, not the user's code base. For searching the user's code base, the agent should use `rg`, its native file search tool, or `lean_local_search`.

### Debugging

When debugging Lean code, the user prefers that agents use the `lean_diagnostics` tool provided by the lean-lsp mcp plugin. This tool provides detailed diagnostics about errors in Lean code, which can be very helpful for debugging. For fixing those errors, the `lean_multi_attempt` tool should be used **whenever possible** as it can try multiple fixes in one go, which is often more efficient than trying out one fix, calling diagnostics again, noticing it is still broken, and repeating. If one fix attempt was made without multi-attempt, then the next attempts should definitely use multi-attempt.

The agent should also be aware of the `lean_hover_info` and `lean_goal` tools.

## Exception for Copilot in VS Code

When the user is using GitHub Copilot in VS Code, they prefer that agents do not use the lean-lsp diagnostics tool, and instead use the native `get_errors` tool provided by VS Code. This is much faster (10x faster). However, if these are insufficient to solve the problem, then the agent can revert to using the lean-lsp mcp plugin tools as a fallback.