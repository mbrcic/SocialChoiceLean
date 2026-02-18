import Pivato.Theorem1.Cones
import Pivato.Theorem1.PairwiseOrders
import Pivato.Theorem1.Representation
import Pivato.Theorem1.Defs
import Pivato.Theorem1.LemmaC1
import Pivato.Theorem1.Skewification
import Pivato.Theorem1.OrderedAdditiveExtension
import Pivato.Theorem1.C1OrderedCodomain

/-!
# Theorem 1

This file states Theorem 1 (Pivato): a variable-population anonymous voting
rule `F` on a weakly-additive domain satisfies reinforcement if and only if
`F` is a (perfect skew) balance rule.

- **`theorem1_forward`**: reinforcement implies a perfect skew balance
  representation (via Lemma C.1 and the ordered-codomain construction).
- **`theorem1_backward`**: a perfect skew balance representation plus weak
  additivity imply reinforcement.
- **`theorem1`**: the biconditional, combining both directions.

The forward direction additionally requires `NonemptyOnDomain` to obtain a
*perfect* (rather than merely minimal) balance representation.
-/

namespace Pivato

universe uV uX

section Theorem1

variable {V : Type uV} {X : Type uX} {D : Domain V} (F : RuleOn D X)

/-- Theorem 1 forward direction: if `F` satisfies reinforcement, then `F`
admits a perfect skew balance representation. -/
theorem theorem1_forward
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hNE : NonemptyOnDomain D F) :
    Reinforcement D F → IsPerfectSkewBalanceRepresentable.{uV, uX, max uV uX} (F := F) :=
  fun hR => lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable (F := F) hD hA hR hNE

/-- Theorem 1 backward direction: a perfect skew balance representation and
weak additivity together imply reinforcement. -/
theorem theorem1_backward
    [DecidableEq V]
    (hWA : WeaklyAdditive D F)
    (hRep : IsPerfectSkewBalanceRepresentable (F := F)) :
    Reinforcement D F :=
  reinforcement_of_perfectSkewBalanceRepresentation (F := F) hWA hRep

/-- **Theorem 1** (Pivato): Let `X` and `V` be arbitrary sets, let `D` be any
domain, and let `F : D ⇒ X` be a variable-population anonymous voting rule for
which `D` is weakly additive. Then `F` satisfies reinforcement if and only if
`F` is a balance rule. -/
theorem theorem1
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F)
    (hNE : NonemptyOnDomain D F)
    (hWA : WeaklyAdditive D F) :
    Reinforcement D F ↔ IsPerfectSkewBalanceRepresentable.{uV, uX, max uV uX} (F := F) :=
  ⟨theorem1_forward (F := F) hD hA hNE, theorem1_backward (F := F) hWA⟩

end Theorem1

end Pivato
