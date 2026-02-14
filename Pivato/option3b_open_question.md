# Open Question (Option 3b): Cone-Based Bridge Needed for Exact Theorem 2

## Setup
Let:
- \(\mathcal X\) be finite,
- \(\mathcal V\) be arbitrary,
- \(\mathcal D \subseteq \mathbb N^{\langle \mathcal V \rangle}\) be a **cone**,
- \(F : \mathcal D \rightrightarrows \mathcal X\) satisfy reinforcement.

For each \(x \in \mathcal X\), define
\[
\mathcal C_x := \{\mathbf d \in \mathcal D : x \in F(\mathbf d)\}.
\]
For each \(x,y \in \mathcal X\), define
\[
\mathcal P_{x,y} := \mathcal C_x - \mathcal C_y \subseteq \mathbb Z^{\langle \mathcal V \rangle},
\qquad
\mathcal O_{x,y} := \mathcal P_{x,y} \cap (-\mathcal P_{x,y}).
\]
Then \(\mathcal O_{x,y}\) is the symmetry subgroup used in Lemma C.1 / Appendix B quotient construction.

## Main Open Question
Is it true that, under the assumptions above (especially that \(\mathcal D\) is a cone),
\[
\mathcal O_{x,y} \text{ is divisible for every } x,y \in \mathcal X?
\]
Equivalently:
\[
\forall n \ge 1,\ \forall z \in \mathbb Z^{\langle \mathcal V \rangle},\quad
n z \in \mathcal O_{x,y} \Rightarrow z \in \mathcal O_{x,y}.
\]

## Why This Matters
A positive answer would yield torsion-freeness of
\[
\mathcal R_{x,y} := \mathbb Z^{\langle \mathcal V \rangle}/\mathcal O_{x,y}
\]
via Appendix B (Cor. B.1(b)-type argument), enabling the homogeneous order-extension step used in Lemma C.1 with no extra assumptions beyond the theorem-level hypotheses.

That would remove the current extra bridge assumptions and recover the paper-strength pipeline to Theorem 2.

## Equivalent / Alternative Sufficient Targets
Any of the following would also suffice:

1. Prove directly that each \(\mathcal R_{x,y}\) is torsion-free under cone + reinforcement hypotheses.
2. Prove torsion-freeness of the aggregated codomain built from all pairwise quotients.
3. Prove a weaker structural property than divisibility that is still enough to apply homogeneous order extension in the required quotients.

## Scope Clarification
Without the cone hypothesis, the analogous claim is false in general (e.g., even-profile domains).
So the question is specifically about the **cone-based** regime needed for Theorem 2.
