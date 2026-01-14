import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.CondorcetLoser

namespace SocialChoice

open Finset

/-!
# IRV Satisfies Independence of Clones

This is a proof that IRV satisfies independence of clones, taken from the paper
"Generalizing Instant Runoff Voting to Allow Indifferences" by Théo Delemazure and Dominik Peters

This proof actually applies to a more general rule defined for weak order input, called Approval-IRV, which reduces to IRV on linear order input. (In Approval-IRV, each voter approves all alternatives in their top indifference class, i.e. gives 1 full point to each of those alternatives. For linear orders, there is always only one such alternative. The proof also works for the linear order case.)

\begin{restatable}{theorem}{AVIRVclones} \label{thm:AVIRVclones}
    Approval-IRV is independent of clones.
\end{restatable}


\begin{proof}
We show that Approval-IRV satisfies independence of clones. Write $f$ for Approval-IRV.

For a profile $P$, we will use the following shorthand notation: For $\ell \in C$, we write $P - \ell$ for the profile $P_{C \setminus \{\ell\}}$ with $\ell$ deleted. For a set $X \subseteq C$, we write $P - X$ for the profile $P|_{C\setminus X}$ with the alternatives in $X$ deleted. Similarly, for $x \in X$, we write $P - X + x$ for the profile $P|_{(C \setminus X) \cup \{x\}}$ with all alternatives in $X$ except for $x$ deleted.

The following lemma connects the scores of the alternatives in the profile $P$ and in the profile $P - X + x$, where $X$ is a clone set. It is the key to the proof working, and other rules like Split-IRV do not have the same property, explaining why the proof does not work for them.

\begin{lemma} \label{lem:clone-scores}
	Let $P$ be a profile defined on alternative set $C$ with clone set $X\subseteq C$. Let $x \in X$. Then
	\begin{itemize}
		\item every $c \in C \setminus X$ has the same approval score in $P$ and $P - X + x$, and
		\item the approval score of $x$ in $P -X +x$ is at least as high as the approval score of every clone alternative $x' \in X$ in $P$.
	\end{itemize}
\end{lemma}
\begin{proof}

	For the first point, observe that for $c \in C \setminus X$, $c$ is ranked in the top indifference class of a voter $i$ in $P$ iff $c \pref_i d$ for all $d \in C$ iff (by definition of clone set) $c \pref_i d$ for all $d \in (C \setminus X) \cup \{x\}$ iff it is ranked in the top indifference class of $i$ in $P - X + x$.

	For the second point, fix $x \in X$ and let $x' \in X$. Then if $x'$ is ranked in the top indifference class of a voter $i$ in $P$, then $x' \pref_i d$ for all $d \in C$ and in particular for all $d \in C \setminus X$. Thus, by definition of clone set, we also have $x \pref_i d$ for all $d \in C \setminus X$, and hence $x$ is ranked in the top indifference class of $i$ in $P - X + x$. So the number of voters with $x'$ in their top indifference class in $P$ is weakly lower than the number with $x$ in their top indifference class in $P - X + x$.
\end{proof}

By induction on $m$, we prove the following statement:

\begin{quote}
	For every profile $P$ defined on a set $C$ of $m$ alternative including a non-empty clone set $X \subseteq C$, the following hold: [$H$ stands for hypothesis]
	\begin{enumerate}
		\item[\quad$H_1(P,X)$:] for all $c \in C \setminus X$, $c \in f(P)$ if and only if $c \in f(P - X + x)$ for all $x \in X$.
		\item[\quad$H_2(P,X)$:] we have $f(P) \cap X \neq \emptyset$ if and only if $x \in f(P - X + x)$ for all $x \in X$.
	\end{enumerate}
\end{quote}

Note that the statement is trivially true if $|X| = 1$ since then $P - X + x = P$. The statement is also obvious when $|X| = |C|$ since then $P - X + x$ is a profile in which only 1 alternative exists. Now, the base case $m = 2$ is easy to see, since then either $|X| = 1$ or $|X| = 2 = |C|$.

So let $m \ge 3$, assume we have shown the statement for $m - 1$, and let $P$ be a profile with $m$ alternatives $C$ including clone set $X \subseteq C$ with $2 \le |X| \le m - 1$.

Let us first note a simple fact that follows because Approval-IRV is a neutral rule (invariant under renaming alternatives). For every non-clone alternative $c \in C \setminus X$, we have
\[
c \in f(P - X + x) \text{ for some $x \in X$} \iff c \in f(P - X + x) \text{ for all $x \in X$},
\]
and we have that
\[
x \in f(P - X + x) \text{ for some $x \in X$} \iff x \in f(P - X + x) \text{ for all $x \in X$}.
\]
This just follows because for two clones $x, x' \in X$, by definition of clone sets, the profiles $P - X + x$ and $P - X + x'$ are identical up to the permutation that exchanges $x$ and $x'$. These equivalences mean that we can use the inductive hypotheses in the ``all $x$'' version but only need to prove them in the ``some $x$'' version.

We first prove $H_1(P, X)$. Let $c \in f(P	) \setminus X$ be a non-clone alternative that wins in $P$. We need to show that $c \in f(P - X + x)$ for some $x \in X$.
Note that by definition of elimination scoring rules, $c \in f(P)$ means that there is an alternative $\ell$ with lowest score in $P$ such that $c \in f(P - \ell)$.
\begin{itemize}
	\item Consider first the case that $\ell$ is not a clone alternative, $\ell \not \in X$. Take any $x \in X$. By \Cref{lem:clone-scores}, $\ell$ is also a lowest-scoring alternative in $P - X + x$. Thus by definition of elimination scoring rules, $f((P - X + x) - \ell) \subseteq f(P - X + x)$, and hence it suffices to show that $c \in f((P - X + x)- \ell) = f((P - \ell) - X + x)$. But this follows from $H_1(P-\ell, X)$ because $c \in f(P - \ell)$.
	\item Consider next the case that $\ell \in X$, and take any $x \in X \setminus \{\ell\}$, which exists since $|X| \ge 2$. Then applying $H_1(P - \ell, X \setminus \{\ell\})$ to $c \in f(P - \ell)$, we get that $c \in f((P - \ell) - (X \setminus \{\ell\}) + x) = f(P - X + x)$ where the last equality follows because the two profiles are the same since $\ell \in X$.
\end{itemize}

Conversely, suppose that $c \in f(P - X + x)$ for all $x \in X$.
\begin{itemize}
	\item Suppose that there exists a clone alternative $x' \in X$ which is a lowest-scoring alternative in $P$. Noting that $|X| \ge 2$, choose any other clone $x \in X \setminus \{x'\}$ and note that $c \in f(P - X + x)$ by assumption. Since $x'$ is lowest-scoring in $P$, by definition of elimination scoring rules, $f(P - x') \subseteq f(P)$. By $H_1(P - x', X \setminus \{x'\})$, it follows from $c \in f(P - X + x) = f((P - x') - (X \setminus \{x'\}) + x)$ that $c \in f(P - x')$ and hence $c \in f(P)$.
	\item Otherwise, only non-clone alternatives are lowest-scoring in $P$. Then by \Cref{lem:clone-scores}, the same is true in $f(P - X + x)$. Since $c \in f(P - X + x)$ and $|X| \le m - 1$, there must be a lowest-scoring alternative $\ell \not \in X$ such that $c \in f((P - X + x) - \ell) = f((P - \ell) - X + x)$. By $H_1(P - \ell, X)$, it follows that $c \in f(P - \ell)$. Because $\ell$ must also be lowest-scoring in $P$ (due to \Cref{lem:clone-scores}), we have $f(P - \ell) \subseteq f(P)$, and hence $c \in f(P)$.
\end{itemize}

We next prove $H_2(P, X)$, using analogous reasoning. Suppose that $f(P) \cap X \neq \emptyset$. Let $x \in f(P) \cap X$ be a winning clone alternative. By definition of elimination scoring rules, $x \in f(P)$ means that there is an alternative $\ell$ with lowest score in $P$ such that $x\in f(P - \ell)$.
We show that $x \in f(P - X + x)$.
\begin{itemize}
	\item Consider first the case that $\ell$ is not a clone alternative, $\ell \not \in X$.
	By \Cref{lem:clone-scores}, $\ell$ is also a lowest-scoring alternative in $P - X + x$. Thus by definition of elimination scoring rules, $f((P - X + x) - \ell) \subseteq f(P - X + x)$, and hence it suffices to show that $x \in f((P - X + x)- \ell) = f((P - \ell) - X + x)$. But this follows from $H_2(P-\ell, X)$ because $x \in f(P - \ell)$.
	\item Consider next the case that $\ell \in X$. Clearly $\ell \neq x$ since $x \in f(P - \ell)$.
	By $H_2(P - \ell, X \setminus \{\ell\})$, since $x \in f(P - \ell)$, we get that $x \in f((P - \ell) - (X \setminus \{\ell\}) + x) = f(P - X + x)$ where the last equality follows because the two profiles are the same since $\ell \in X$.
\end{itemize}

Conversely, suppose that $x \in f(P - X + x)$ for all $x \in X$. We need to show that $f(P) \cap X \neq \emptyset$.
\begin{itemize}
	\item Suppose that there exists a clone alternative $x' \in X$ which is a lowest-scoring alternative in $P$.
	Noting that $|X| \ge 2$, choose any other clone $x \in X \setminus \{x'\}$ and note that $x \in f(P - X + x)$ by assumption.
	Since $x'$ is lowest-scoring in $P$, by definition of elimination scoring rules, $f(P - x') \subseteq f(P)$. By $H_2(P - x', X \setminus \{x'\})$, it follows from $x \in f(P - X + x) = f((P - x') - (X \setminus \{x'\}) + x)$ that $f(P - x') \cap (X \setminus \{x'\}) \neq \emptyset$ and hence also $f(P) \cap X \neq \emptyset$.
	\item Otherwise, only non-clone alternatives are lowest-scoring in $P$. Then by \Cref{lem:clone-scores}, the same is true in $f(P - X + x)$. Since $x \in f(P - X + x)$ and $|X| \le m - 1$, there must be a lowest-scoring alternative $\ell \not \in X$ such that $x \in f((P - X + x) - \ell) = f((P - \ell) - X + x)$. By $H_2(P - \ell, X)$, it follows that $f(P - \ell) \cap X \neq \emptyset$. Because $\ell$ must also be lowest-scoring in $P$ (due to \Cref{lem:clone-scores}), we have $f(P - \ell) \subseteq f(P)$, and hence also $f(P) \cap X \neq \emptyset$. \qedhere
\end{itemize}
\end{proof}
-/

variable {V A : Type} [Fintype V] [Fintype A]

noncomputable instance instDecidablePredClone {A : Type} (X : Set A) (x : A) :
    DecidablePred (fun a : A => a ∉ X ∨ a = x) := by
  classical
  infer_instance

def clonePred (X : Set A) (x : A) : A → Prop := fun a => a ∉ X ∨ a = x

noncomputable instance instDecidablePredClonePred {A : Type} (X : Set A) (x : A) :
    DecidablePred (clonePred X x) := by
  classical
  simpa [clonePred] using (instDecidablePredClone (A := A) X x)

noncomputable instance instFintypeClonePred {A : Type} [Fintype A] (X : Set A) (x : A) :
    Fintype {a : A // clonePred X x a} := by
  classical
  infer_instance

noncomputable instance instDecidableEqCloneSubtype {A : Type} (X : Set A) (x : A) :
    DecidableEq {a : A // clonePred X x a} := by
  classical
  exact Classical.decEq _

/-! ## Clone sets and restriction helpers -/

/-- A clone set `X` (subset of candidates). -/
def CloneSet (P : Profile V A) (X : Set A) : Prop :=
  X.Nonempty ∧
    ∀ v c, c ∉ X →
      (∀ x ∈ X, Prefers P v x c) ∨ (∀ x ∈ X, Prefers P v c x)

/-- Remove all clones in `X` except for the representative `x`. -/
noncomputable def removeClonesExcept (P : Profile V A) (X : Set A) (x : A) :
    Profile V {a : A // clonePred X x a} :=
  restrictCandidates P (clonePred X x)

lemma clonePred_swap {A : Type} [DecidableEq A] (X : Set A) (x x' a : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    clonePred X x a ↔ clonePred X x' ((Equiv.swap x x') a) := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [clonePred, Equiv.swap_apply_left]
  · by_cases hax' : a = x'
    · subst hax'
      simp [clonePred, Equiv.swap_apply_right, hxx', hx, hx', hax]
    · have hswap : (Equiv.swap x x') a = a := by
        simp [Equiv.swap_apply_def, hax, hax']
      simp [clonePred, hswap, hax, hax']

noncomputable def cloneSwapEquiv {A : Type} [DecidableEq A]
    (X : Set A) (x x' : A) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    {a : A // clonePred X x a} ≃ {a : A // clonePred X x' a} :=
  (Equiv.swap x x').subtypeEquiv (clonePred_swap (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx'))

lemma relabelProfile_removeClonesExcept_swap_rep
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hX : CloneSet P X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    relabelProfile (removeClonesExcept P X x)
        (cloneSwapEquiv X x x' hx hx' hxx') =
      removeClonesExcept P X x' := by
  classical
  let e := cloneSwapEquiv X x x' hx hx' hxx'

  -- Helper: clones are interchangeable when comparing to a non-clone.
  have hclone_eq :
      ∀ v c, c ∉ X →
        (Prefers P v x c ↔ Prefers P v x' c) ∧ (Prefers P v c x ↔ Prefers P v c x') := by
    intro v c hc
    -- Work in the linear order given by voter `v`.
    let _ := P.pref v
    rcases hX with ⟨_, hclone⟩
    have hcase := hclone v c hc
    cases hcase with
    | inl hall =>
        have hxpref : Prefers P v x c := hall x hx
        have hx'pref : Prefers P v x' c := hall x' hx'
        have hxfalse : ¬ Prefers P v c x := by
          intro h
          exact lt_asymm hxpref h
        have hx'false : ¬ Prefers P v c x' := by
          intro h
          exact lt_asymm hx'pref h
        refine ⟨?_, ?_⟩
        · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩
        · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
    | inr hall =>
        have hxpref : Prefers P v c x := hall x hx
        have hx'pref : Prefers P v c x' := hall x' hx'
        have hxfalse : ¬ Prefers P v x c := by
          intro h
          exact lt_asymm h hxpref
        have hx'false : ¬ Prefers P v x' c := by
          intro h
          exact lt_asymm h hx'pref
        refine ⟨?_, ?_⟩
        · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
        · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩

  -- Helper: `e.symm` fixes non-clones.
  have esymm_nonclone :
      ∀ {c : A} (hc : c ∉ X),
        e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) =
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
    intro c hc
    have hcx : c ≠ x := by
      intro h
      apply hc
      simpa [h] using hx
    have hcx' : c ≠ x' := by
      intro h
      apply hc
      simpa [h] using hx'
    apply Subtype.ext
    -- `e.symm` is induced by `swap x x'`, which fixes non-clones.
    simp [e, cloneSwapEquiv, Equiv.swap_apply_def, hcx, hcx']

  -- Helper: `e.symm` sends the representative `x'` back to `x`.
  have esymm_rep :
      e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) =
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
    apply Subtype.ext
    simp [e, cloneSwapEquiv, Equiv.swap_apply_right]

  -- Main proof: ext by ballots and compare `<`.
  ext v : 1
  apply LinearOrder.ext_lt
  intro a b
  let _ := P.pref v
  change Prefers P v (e.symm a) (e.symm b) ↔ Prefers P v a b
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      cases ha with
      | inl ha_not =>
        cases hb with
        | inl hb_not =>
          have ha_fix := esymm_nonclone (c := a) ha_not
          have hb_fix := esymm_nonclone (c := b) hb_not
          simp [ha_fix, hb_fix]
        | inr hb_eq =>
          subst hb_eq
          have ha_fix := esymm_nonclone (c := a) ha_not
          have hrel := (hclone_eq v a ha_not).2
          simpa [ha_fix, esymm_rep] using hrel
      | inr ha_eq =>
        subst ha_eq
        cases hb with
        | inl hb_not =>
          have hb_fix := esymm_nonclone (c := b) hb_not
          have hrel := (hclone_eq v b hb_not).1
          simpa [hb_fix, esymm_rep] using hrel
        | inr hb_eq =>
          subst hb_eq
          have hleft : ¬ Prefers P v x x := by
            simpa [Prefers] using (lt_irrefl (a := x))
          have hright : ¬ Prefers P v b b := by
            simpa [Prefers] using (lt_irrefl (a := b))
          constructor
          · intro h
            have h' : Prefers P v x x := by
              simpa [esymm_rep] using h
            exact (hleft h').elim
          · intro h
            exact (hright h).elim

lemma cloneSwapEquiv_apply_nonclone {A : Type} [DecidableEq A]
    {X : Set A} {x x' c : A} (hc : c ∉ X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨c, Or.inl hc⟩ = ⟨c, Or.inl hc⟩ := by
  classical
  have hcx : c ≠ x := by
    intro h
    apply hc
    simpa [h] using hx
  have hcx' : c ≠ x' := by
    intro h
    apply hc
    simpa [h] using hx'
  have hswap : (Equiv.swap x x') c = c := by
    simp [Equiv.swap_apply_def, hcx, hcx']
  ext
  simp [cloneSwapEquiv, hswap]

lemma cloneSwapEquiv_apply_rep {A : Type} [DecidableEq A]
    {X : Set A} {x x' : A} (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨x, Or.inr rfl⟩ = ⟨x', Or.inr rfl⟩ := by
  classical
  ext
  simp [cloneSwapEquiv, Equiv.swap_apply_left]

/-- Clone set on a restricted candidate type. -/
def restrictCloneSet (X : Set A) (ℓ : A) : Set {a : A // a ≠ ℓ} :=
  {a | (a : A) ∈ X}

omit [Fintype A] in
@[simp] lemma mem_restrictCloneSet {X : Set A} {ℓ : A} {a : {a : A // a ≠ ℓ}} :
    a ∈ restrictCloneSet X ℓ ↔ (a : A) ∈ X := by
  rfl

@[simp] lemma prefers_removeClonesExcept_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) (v : V)
    (a b : {a : A // clonePred X x a}) :
    Prefers (removeClonesExcept P X x) v a b ↔ Prefers P v a b := by
  rfl

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {a : A} (ha : p a) :
    a ∈ liftWinners s ↔ (⟨a, ha⟩ : {a : A // p a}) ∈ s := by
  classical
  -- `liftWinners` is `image Subtype.val`.
  simp [liftWinners, Finset.mem_image, ha]

omit [Fintype A] in
lemma restrictCloneSet_nonempty {X : Set A} {ℓ : A}
    (h : ∃ x ∈ X, x ≠ ℓ) : (restrictCloneSet X ℓ).Nonempty := by
  rcases h with ⟨x, hx, hxne⟩
  refine ⟨⟨x, hxne⟩, ?_⟩
  simpa [restrictCloneSet] using hx

lemma cloneSet_restrictProfile
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (ℓ : A) (hX : CloneSet P X)
    (hXne : ∃ x ∈ X, x ≠ ℓ) :
    CloneSet (restrictProfile P ℓ) (restrictCloneSet X ℓ) := by
  classical
  rcases hX with ⟨_hXnonempty, hclone⟩
  refine ⟨restrictCloneSet_nonempty (X := X) (ℓ := ℓ) hXne, ?_⟩
  intro v c hc
  have hc' : (c : A) ∉ X := by
    intro hmem
    apply hc
    simpa [restrictCloneSet] using hmem
  have hcase := hclone v (c : A) hc'
  cases hcase with
  | inl hall =>
    left
    intro x hx
    have hx' : (x : A) ∈ X := by
      simpa [restrictCloneSet] using hx
    simpa using (hall x hx')
  | inr hall =>
    right
    intro x hx
    have hx' : (x : A) ∈ X := by
      simpa [restrictCloneSet] using hx
    simpa using (hall x hx')

lemma scoringEliminationAux_swap_rep
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    scoringEliminationAux pluralityScore _
        (relabelProfile (removeClonesExcept P X x)
          (cloneSwapEquiv X x x' hx hx' hxx')) =
      (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
        (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding := by
  classical
  have h :=
    scoringEliminationAux_equiv (score := pluralityScore)
      (P := removeClonesExcept P X x) (e := cloneSwapEquiv X x x' hx hx' hxx')
  simpa using h

lemma nonclone_winner_swap
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' c : A)
    (hc : c ∉ X) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
    classical
  let e := cloneSwapEquiv X x x' hx hx' hxx'
  have hswap := scoringEliminationAux_swap_rep (P := P) (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx')
  have hmem :
      (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          e.toEmbedding ↔
      e.symm
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
    mem_relabelWinners (e := e) _ _
  have hfix :
      e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) =
        (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
    have hfix' := cloneSwapEquiv_apply_nonclone (X := X) (x := x) (x' := x')
      (c := c) (hc := hc) (hx := hx) (hx' := hx') (hxx' := hxx')
    have hleft := e.left_inv ⟨c, Or.inl hc⟩
    simpa [e, hfix'] using hleft
  constructor
  · intro hcwin
    have hcwin_map : (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          e.toEmbedding :=
      hmem.mpr (by simpa [hfix] using hcwin)
    simpa [hswap, e] using hcwin_map
  · intro hcwin
    have hcwin_map : (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          e.toEmbedding := by
      simpa [hswap, e] using hcwin
    have hcwin_pre := hmem.mp hcwin_map
    simpa [hfix] using hcwin_pre

lemma clone_winner_swap
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
  classical
  let e := cloneSwapEquiv X x x' hx hx' hxx'
  have hswap := scoringEliminationAux_swap_rep (P := P) (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx')
  have hmem :
      (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
        (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
          e.toEmbedding ↔
      e.symm
          (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
    mem_relabelWinners (e := e) _ _
  have hsymm :
      e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) =
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
    have hrep := cloneSwapEquiv_apply_rep (X := X) (x := x) (x' := x')
      (hx := hx) (hx' := hx') (hxx' := hxx')
    have hleft := e.left_inv ⟨x, Or.inr rfl⟩
    simpa [e, hrep] using hleft
  constructor
  · intro hxwin
    have hxwin_map :
        (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
          (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
            e.toEmbedding :=
      hmem.mpr (by simpa [hsymm] using hxwin)
    simpa [hswap, e] using hxwin_map
  · intro hxwin
    have hxwin_map :
        (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
          (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
            e.toEmbedding := by
      simpa [hswap, e] using hxwin
    have hxwin_pre := hmem.mp hxwin_map
    simpa [hsymm] using hxwin_pre


/-! ## Plurality score facts under clone restriction -/

noncomputable def pluralityScoreVec : Nat → Int :=
  fun r => if r = 0 then 1 else 0

lemma cloneSet_prefers_equiv
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x x' y : A} (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∉ X) (v : V) :
    (Prefers P v x y ↔ Prefers P v x' y) ∧
      (Prefers P v y x ↔ Prefers P v y x') := by
  classical
  rcases hX with ⟨_, hclone⟩
  let _ := P.pref v
  have hcase := hclone v y hy
  cases hcase with
  | inl hall =>
    have hxpref : Prefers P v x y := hall x hx
    have hx'pref : Prefers P v x' y := hall x' hx'
    have hxfalse : ¬ Prefers P v y x := by
      intro h
      exact lt_asymm (hall x hx) h
    have hx'false : ¬ Prefers P v y x' := by
      intro h
      exact lt_asymm (hall x' hx') h
    refine ⟨?_, ?_⟩
    · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩
    · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
  | inr hall =>
    have hxpref : Prefers P v y x := hall x hx
    have hx'pref : Prefers P v y x' := hall x' hx'
    have hxfalse : ¬ Prefers P v x y := by
      intro h
      exact lt_asymm h (hall x hx)
    have hx'false : ¬ Prefers P v x' y := by
      intro h
      exact lt_asymm h (hall x' hx')
    refine ⟨?_, ?_⟩
    · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
    · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩

lemma topRank_removeClonesExcept_iff_of_nonclone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) (v : V) :
    TopRank P v a ↔
      TopRank (removeClonesExcept P X x) v (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) := by
  classical
  constructor
  · intro htop d hd
    have := htop d (by
      intro hEq
      apply hd
      ext
      simpa using hEq)
    simpa using this
  · intro htop d hd
    by_cases hdx : d ∈ X
    · -- If `d` is a clone, use clone symmetry and the fact that `x` is in the restricted profile.
      have hxa : Prefers P v a x := by
        have htop' := htop (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) (by
          intro hEq
          apply ha
          have hxEq : x = a := congrArg Subtype.val hEq
          simpa [hxEq] using hx)
        simpa using htop'
      have hrel :=
        (cloneSet_prefers_equiv P X hX hdx hx ha v).2
      -- `Prefers P v a d ↔ Prefers P v a x`
      exact (hrel.mpr hxa)
    · -- `d` is a non-clone, so it appears in the restricted profile.
      have htop' := htop (⟨d, Or.inl hdx⟩ : {a : A // clonePred X x a}) (by
        intro hEq
        apply hd
        simpa using congrArg Subtype.val hEq)
      simpa using htop'

lemma topRank_clone_implies_rep
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) (v : V) :
    TopRank P v y →
      TopRank (removeClonesExcept P X x) v (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
  classical
  intro htop d hd
  by_cases hdx : (d : A) ∈ X
  · -- Only `x` from `X` remains; the other case is `d = x`.
    have hxEq : (d : A) = x := by
      cases d.property with
      | inl hnot =>
        exact (hnot hdx).elim
      | inr hEq =>
        exact hEq
    exact (hd (by
      ext
      simpa using hxEq)).elim
  · -- For non-clones, use clone symmetry with `y`.
    have hrel := (cloneSet_prefers_equiv P X hX hy hx hdx v).1
    have hy_top : Prefers P v y d := htop d (by
      intro hEq
      apply hdx
      simpa [hEq] using hy)
    exact (hrel.mp hy_top)

lemma votersTop_card_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) :
    (votersTop P a).card =
      (votersTop (removeClonesExcept P X x) (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})).card := by
  classical
  refine cardinality_lemma2 (p := fun v => TopRank P v a)
    (q := fun v =>
      TopRank (removeClonesExcept P X x) v (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})) ?_
  intro v
  exact topRank_removeClonesExcept_iff_of_nonclone P X x hX hx ha v

lemma votersTop_card_rep_ge_clone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) :
    (votersTop P y).card ≤
      (votersTop (removeClonesExcept P X x) (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card := by
  classical
  refine cardinality_lemma (p := fun v => TopRank P v y)
    (q := fun v =>
      TopRank (removeClonesExcept P X x) v (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})) ?_
  intro v hv
  exact topRank_clone_implies_rep P X x y hX hx hy v hv

lemma score_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) :
    scoreCandidate P pluralityScoreVec a =
      scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
        (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) := by
  classical
  have hcard :=
    votersTop_card_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := ha)
  calc
    scoreCandidate P pluralityScoreVec a
        = ((votersTop P a).card : Int) := by
            simpa [pluralityScoreVec] using (pluralityScore_eq_votersTop_card (P := P) (c := a))
    _ = ((votersTop (removeClonesExcept P X x)
            (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})).card : Int) := by
            exact_mod_cast hcard
    _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) := by
            symm
            simpa [pluralityScoreVec] using
              (pluralityScore_eq_votersTop_card (P := removeClonesExcept P X x)
                (c := (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})))

lemma score_rep_ge_clone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) :
    scoreCandidate P pluralityScoreVec y ≤
      scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
  classical
  have hcard :=
    votersTop_card_rep_ge_clone (P := P) (X := X) (x := x) (y := y) (hX := hX) (hx := hx) (hy := hy)
  have hcard' : (votersTop P y).card ≤
      (votersTop (removeClonesExcept P X x)
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card := hcard
  have hcardInt :
      ((votersTop P y).card : Int) ≤
        ((votersTop (removeClonesExcept P X x)
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card : Int) := by
    exact_mod_cast hcard'
  calc
    scoreCandidate P pluralityScoreVec y
        = ((votersTop P y).card : Int) := by
            simpa [pluralityScoreVec] using (pluralityScore_eq_votersTop_card (P := P) (c := y))
    _ ≤ ((votersTop (removeClonesExcept P X x)
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card : Int) := hcardInt
    _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          symm
          simpa [pluralityScoreVec] using
            (pluralityScore_eq_votersTop_card (P := removeClonesExcept P X x)
              (c := (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})))

/-! ## Lowest-scoring characterization -/

lemma lowestScoring_iff_forall_le {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int)
    (hA : (Finset.univ : Finset A).Nonempty) (c : A) :
    c ∈ lowestScoring P score ↔
      ∀ d : A, scoreCandidate P score c ≤ scoreCandidate P score d := by
  classical
  let scoreSet : Finset Int := Finset.univ.image (fun a => scoreCandidate P score a)
  have hScoreNonempty : scoreSet.Nonempty := by
    simpa [scoreSet, Finset.Nonempty] using hA.image (fun a => scoreCandidate P score a)
  let minScore : Int := scoreSet.min' hScoreNonempty
  constructor
  · intro hc d
    have hc' : scoreCandidate P score c = minScore := by
      simpa [lowestScoring, hA, scoreSet, minScore] using hc
    have hmem : scoreCandidate P score d ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score d :=
      Finset.min'_le scoreSet _ hmem
    simpa [hc'] using hminle
  · intro hle
    have hmem : scoreCandidate P score c ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score c :=
      Finset.min'_le scoreSet _ hmem
    have hmin_mem : minScore ∈ scoreSet := Finset.min'_mem scoreSet hScoreNonempty
    rcases Finset.mem_image.mp hmin_mem with ⟨d, _hd, hdeq⟩
    have hle' : scoreCandidate P score c ≤ minScore := by
      simpa [hdeq] using hle d
    have hmin_eq : scoreCandidate P score c = minScore := le_antisymm hle' hminle
    have hc : c ∈ (Finset.univ.filter (fun a => scoreCandidate P score a = minScore)) := by
      exact Finset.mem_filter.mpr ⟨by simp, hmin_eq⟩
    simpa [lowestScoring, hA, scoreSet, minScore] using hc

lemma lowestScoring_nonclone_preserved
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {ℓ : A} (hℓ : ℓ ∉ X)
    (hℓ_low : ℓ ∈ lowestScoring P pluralityScoreVec) :
    (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}) ∈
      lowestScoring (removeClonesExcept P X x) pluralityScoreVec := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := by
    rcases hX.1 with ⟨y, _⟩
    have : Nonempty A := ⟨y⟩
    exact Finset.univ_nonempty
  have hAhat : (Finset.univ : Finset {a : A // clonePred X x a}).Nonempty := by
    letI : Nonempty {a : A // clonePred X x a} := ⟨⟨x, Or.inr rfl⟩⟩
    exact Finset.univ_nonempty
  have hℓ_low' :
      ∀ d : A, scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec d :=
    (lowestScoring_iff_forall_le (P := P) (score := pluralityScoreVec) hA ℓ).1 hℓ_low
  have hle :
      ∀ d : {a : A // clonePred X x a},
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})
          ≤ scoreCandidate (removeClonesExcept P X x) pluralityScoreVec d := by
    intro d
    cases d.property with
    | inl hdnot =>
      have hℓ_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      have hd_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hdnot)
      calc
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})
            = scoreCandidate P pluralityScoreVec ℓ := by
                symm
                exact hℓ_eq
        _ ≤ scoreCandidate P pluralityScoreVec d := hℓ_low' d
        _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨d, Or.inl hdnot⟩ : {a : A // clonePred X x a}) := by
                exact hd_eq
    | inr hdx =>
      have hℓ_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      have hx_le :=
        score_rep_ge_clone (P := P) (X := X) (x := x) (y := x) (hX := hX) (hx := hx) (hy := hx)
      have hℓx : scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec x :=
        hℓ_low' x
      have hxEq : (d : A) = x := hdx
      have hdEq : d = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
        ext
        simp [hxEq]
      calc
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})
            = scoreCandidate P pluralityScoreVec ℓ := by
                symm
                exact hℓ_eq
        _ ≤ scoreCandidate P pluralityScoreVec x := hℓx
        _ ≤ scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := hx_le
        _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec d := by
              simp [hdEq]
  exact (lowestScoring_iff_forall_le (P := removeClonesExcept P X x)
      (score := pluralityScoreVec) hAhat
      (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})).2 hle

/-! ## Main induction (proof sketch) -/

def irv_nonclone_prop
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  ∀ a (ha : a ∉ X),
    a ∈ scoringEliminationAux pluralityScore A P ↔
      (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)

def irv_clone_prop
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  (∃ y, y ∈ X ∧ y ∈ scoringEliminationAux pluralityScore A P) ↔
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
      scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)

def independence_of_clones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
      (P : Profile V A) (X : Set A) (x : A),
    CloneSet P X → x ∈ X →
      (∀ c (hc : c ∉ X),
        (c ∈ f P ↔
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ f (removeClonesExcept P X x))) ∧
      ((∃ y, y ∈ X ∧ y ∈ f P) ↔
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ f (removeClonesExcept P X x))

/-! ## Basic nonemptiness of IRV winners -/

lemma scoringEliminationAux_nonempty
    (score : Nat → Nat → Int)
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : Profile V A) :
    (scoringEliminationAux score A P).Nonempty := by
  classical
  -- Strong induction on the number of candidates.
  set n := Fintype.card A with hn
  -- Motive generalized over candidate types of a given cardinality.
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A'] [Nonempty A']
      {V' : Type} [Fintype V']
      (P' : Profile V' A'),
        Fintype.card A' = k → (scoringEliminationAux score A' P').Nonempty
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ _ V' _ P' hk
    by_cases hle : Fintype.card A' ≤ 1
    · -- Base case: definition returns `univ`.
      have hdef : scoringEliminationAux score A' P' = (Finset.univ : Finset A') := by
        simp [scoringEliminationAux, hle]
      rw [hdef]
      exact (Finset.univ_nonempty : (Finset.univ : Finset A').Nonempty)
    · -- Recursive case: pick a lowest-scoring candidate and recurse.
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := score) (P := P') (hcard := hle)
      -- Unpack the RHS.
      classical
      let m := Fintype.card A'
      let scoreVec : Nat → Int := fun r => score m r
      let L : Finset A' := lowestScoring P' scoreVec
      have hLne : L.Nonempty := by
        apply lowestScoring_nonempty
        exact (Finset.univ_nonempty : (Finset.univ : Finset A').Nonempty)
      rcases hLne with ⟨ℓ, hℓL⟩
      -- Apply IH on the restricted candidate type.
      have hcard_sub_lt : Fintype.card {x : A' // x ≠ ℓ} < Fintype.card A' :=
        card_restrict_lt ℓ
      have hrec : (scoringEliminationAux score {x : A' // x ≠ ℓ} (restrictProfile P' ℓ)).Nonempty := by
        -- IH expects a strict smaller cardinality.
        have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
          -- `card {x // x ≠ ℓ} < card A' = k`.
          simpa [hk] using hcard_sub_lt
        haveI : Nonempty {x : A' // x ≠ ℓ} := by
          -- Since `card A' > 1` in this branch, removing one element leaves something.
          have : 0 < Fintype.card {x : A' // x ≠ ℓ} := by
            have hposA : 1 < Fintype.card A' := by omega
            have hsub := card_subtype_ne_eq ℓ
            -- card subtype = card A' - 1
            have : Fintype.card {x : A' // x ≠ ℓ} = Fintype.card A' - 1 := hsub
            -- hence positive
            omega
          exact Fintype.card_pos_iff.mp this
        exact ih (Fintype.card {x : A' // x ≠ ℓ}) hklt (P' := restrictProfile P' ℓ) rfl
      rcases hrec with ⟨w, hw⟩
      -- Build an element in the biUnion.
      refine ⟨(w : A'), ?_⟩
      -- Rewrite using `haux` and show membership in the RHS.
      -- (We avoid `simp` over the `let`s by unfolding them locally.)
      have hw_lift : (w : A') ∈ liftFinset (scoringEliminationAux score _ (restrictProfile P' ℓ)) := by
        -- `liftFinset` is `image Subtype.val`.
        refine Finset.mem_image.mpr ?_
        exact ⟨w, hw, rfl⟩
      -- Now place it into the biUnion.
      have : (w : A') ∈
          (lowestScoring P' scoreVec).biUnion
            (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P' c))) := by
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨ℓ, ?_, ?_⟩
        · simpa [L, scoreVec, m] using hℓL
        · simpa [scoreVec, m] using hw_lift
      -- Convert back to the LHS using `haux`.
      simpa [haux, m, scoreVec, L] using this
  -- Specialize the strong induction result.
  simpa [hn] using (hStrong (P' := P) rfl)

  /-! ## Restriction commutation helpers (up to relabeling) -/

  @[simp] lemma clonePred_restrictCloneSet_eq
    {A : Type} (X : Set A) (x ℓ : A) (hxℓ : x ≠ ℓ) :
    clonePred (restrictCloneSet (A := A) X ℓ) (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) =
      (fun a : {a : A // a ≠ ℓ} => clonePred X x a.1) := by
    funext a
    apply propext
    constructor
    · intro h
      rcases h with h | h
      · left
        intro haX
        apply h
        simpa [restrictCloneSet] using haX
      · right
        -- equality in a subtype is equality of values
        exact congrArg Subtype.val h
    · intro h
      rcases h with h | h
      · left
        intro haX
        apply h
        simpa [restrictCloneSet] using haX
      · right
        -- build equality in the subtype
        ext
        simpa using h

  /-- Deleting a non-clone candidate commutes with clone-removal (up to relabeling). -/
  lemma relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x ℓ : A)
    (hxℓ : x ≠ ℓ) (hℓ : ℓ ∉ X) :
    ∃ e,
      (∀ t,
        ((e t).1 : {a : A // a ≠ ℓ}).1 = ((t.1 : {a : A // clonePred X x a}).1)) ∧
      (∀ b,
        ((e.symm b).1 : {a : A // clonePred X x a}).1 = ((b.1 : {a : A // a ≠ ℓ}).1)) ∧
      relabelProfile
          (restrictProfile (removeClonesExcept P X x)
            (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}))
          e =
        removeClonesExcept (restrictProfile P ℓ) (restrictCloneSet X ℓ)
          (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) := by
    classical
    let p : A → Prop := clonePred X x
    let q : A → Prop := fun a => a ≠ ℓ
    let ℓ' : {a : A // p a} := ⟨ℓ, Or.inl hℓ⟩
    let xℓ' : {a : A // q a} := ⟨x, hxℓ⟩
    let e_val : {t : {a : A // p a} // t ≠ ℓ'} ≃ {t : {a : A // p a} // q t.1} :=
      Equiv.subtypeEquivRight (fun t => by
        constructor
        · intro ht
          have : t.1 ≠ ℓ := by
            intro hEq
            apply ht
            ext
            simp [ℓ', hEq]
          exact this
        · intro ht hEq
          apply ht
          simpa using congrArg Subtype.val hEq)
    let e1 : {t : {a : A // p a} // q t.1} ≃ {a : A // p a ∧ q a} :=
      Equiv.subtypeSubtypeEquivSubtypeInter p q
    let ecomm : {a : A // p a ∧ q a} ≃ {a : A // q a ∧ p a} :=
      Equiv.subtypeEquivRight (fun a => by
        constructor <;> intro h <;> simpa [And.comm] using h)
    let e2 : {t : {a : A // q a} // p t.1} ≃ {a : A // q a ∧ p a} :=
      Equiv.subtypeSubtypeEquivSubtypeInter q p
    let e_mid : {t : {a : A // p a} // t ≠ ℓ'} ≃ {t : {a : A // q a} // p t.1} :=
      e_val.trans (e1.trans (ecomm.trans e2.symm))
    let e_right :
        {t : {a : A // q a} // p t.1} ≃
          {t : {a : A // q a} // clonePred (restrictCloneSet X ℓ) xℓ' t} :=
      Equiv.subtypeEquivRight (fun t => by
        have hpred :
            clonePred (restrictCloneSet X ℓ) xℓ' t ↔ clonePred X x t.1 := by
          have := congrArg (fun f => f t)
            (clonePred_restrictCloneSet_eq (X := X) (x := x) (ℓ := ℓ) (hxℓ := hxℓ))
          exact (Iff.of_eq this)
        simpa [p] using hpred.symm)
    let e : {t : {a : A // p a} // t ≠ ℓ'} ≃
        {t : {a : A // q a} // clonePred (restrictCloneSet X ℓ) xℓ' t} :=
      e_mid.trans e_right
    refine ⟨e, ?_, ?_, ?_⟩
    · intro t
      rfl
    · intro b
      rfl
    -- Unfold both sides; the induced restricted orders coincide definitionally.
    ext v
    rfl

  /-- If `ℓ` is a clone different from the representative `x`, then deleting `ℓ` before
  removing clones is redundant (up to relabeling). -/
  lemma relabelProfile_removeClonesExcept_restrictProfile_of_clone
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x ℓ : A)
    (hℓ : ℓ ∈ X) (hxℓ : x ≠ ℓ) :
    ∃ e,
      (∀ t,
        (((e t).1 : {a : A // a ≠ ℓ}).1) = t.1) ∧
      (∀ b,
        (e.symm b).1 = b.1.1) ∧
      relabelProfile (removeClonesExcept P X x) e =
        removeClonesExcept (restrictProfile P ℓ) (restrictCloneSet X ℓ)
          (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) := by
    classical
    -- Build an explicit equivalence between the two restricted candidate types.
    let xℓ' : {a : A // a ≠ ℓ} := ⟨x, hxℓ⟩
    let e : {a : A // clonePred X x a} ≃
      {a : {a : A // a ≠ ℓ} // clonePred (restrictCloneSet X ℓ) xℓ' a} :=
      { toFun := fun t =>
          -- `t.1` cannot be `ℓ`, since `ℓ ∈ X` and `x ≠ ℓ`.
          let hne : (t.1 : A) ≠ ℓ := by
            intro hEq
            have htX : clonePred X x ℓ := by
              simpa [hEq] using t.2
            -- But `clonePred X x ℓ` would imply `ℓ ∉ X` or `ℓ = x`.
            rcases htX with htX | htX
            · exact htX hℓ
            · exact hxℓ (htX.symm)
          have hp' : clonePred (restrictCloneSet X ℓ) xℓ' (⟨t.1, hne⟩ : {a : A // a ≠ ℓ}) := by
            -- Convert the predicate using the simp lemma.
            have hpred :
                clonePred (restrictCloneSet X ℓ) xℓ' (⟨t.1, hne⟩ : {a : A // a ≠ ℓ}) ↔
                  clonePred X x (t.1 : A) := by
              have := congrArg (fun f => f (⟨t.1, hne⟩ : {a : A // a ≠ ℓ}))
                (clonePred_restrictCloneSet_eq (X := X) (x := x) (ℓ := ℓ) (hxℓ := hxℓ))
              exact Iff.of_eq this
            exact (hpred.mpr t.2)
          ⟨⟨t.1, hne⟩, hp'⟩
        invFun := fun s =>
          -- Forget the extra `≠ ℓ` packaging.
          let hpred : clonePred X x (s.1.1 : A) := by
            have hpred' :
                clonePred (restrictCloneSet X ℓ) xℓ' (s.1 : {a : A // a ≠ ℓ}) ↔
                  clonePred X x (s.1.1 : A) := by
              have := congrArg (fun f => f (s.1 : {a : A // a ≠ ℓ}))
                (clonePred_restrictCloneSet_eq (X := X) (x := x) (ℓ := ℓ) (hxℓ := hxℓ))
              exact Iff.of_eq this
            exact (hpred'.1 s.2)
          ⟨s.1.1, hpred⟩
        left_inv := by
          intro t
          ext
          rfl
        right_inv := by
          intro s
          ext
          rfl }
    refine ⟨e, ?_, ?_, ?_⟩
    · intro t
      rfl
    · intro b
      rfl
    ext v
    rfl

  lemma relabelProfile_restrictCandidates_subtypeSubtypeEquivSubtypeInter
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A)
    (p q : A → Prop) [DecidablePred p] [DecidablePred q] :
    relabelProfile (restrictCandidates (restrictCandidates P p) (fun x : {a : A // p a} => q x.1))
      (Equiv.subtypeSubtypeEquivSubtypeInter p q) =
      restrictCandidates P (fun a : A => p a ∧ q a) := by
    ext v
    rfl

/-! ## Main induction proof -/

/-- Combined clone properties as a single proposition for induction. -/
def clone_independence_props
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  irv_nonclone_prop P X x ∧ irv_clone_prop P X x

omit [Fintype A] in
/-- The type `{a // clonePred X x a}` equals `{a // a ∉ X ∨ a = x}` -/
lemma clonePred_eq_or (X : Set A) (x : A) :
  clonePred X x = fun a => a ∉ X ∨ a = x := rfl

/-- Key lemma: winning as non-clone is independent of representative choice (via relabeling). -/
lemma nonclone_winner_rep_independent
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' c : A)
    (hc : c ∉ X) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
  classical
  simpa using nonclone_winner_swap P X x x' c hc hx hx' hxx'

/-! Key lemma: clone winner status is independent under relabeling. -/
lemma clone_winner_rep_independent
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
  classical
  simpa using
    clone_winner_swap (P := P) (X := X) (x := x) (x' := x')
      (hx := hx) (hx' := hx') (hxx' := hxx')


theorem irv_independence_of_clones :
    @independence_of_clones (scoringEliminationRule pluralityScore) := by
  unfold independence_of_clones
  intro V A instV instA instDecEq P₀ X x hX hx
  classical
  -- `scoringEliminationRule` uses `Classical.decEq` internally; align all `DecidableEq` instances.
  letI : DecidableEq A := Classical.decEq A
  -- We prove by strong induction on the number of candidates
  set n := Fintype.card A with hn
  -- Define the motive for strong induction
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A'],
      Fintype.card A' = k →
        ∀ {V' : Type} [Fintype V'] (P' : Profile V' A') (X' : Set A') (x' : A'),
          CloneSet P' X' → x' ∈ X' → clone_independence_props P' X' x'
  -- Strong induction
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ hcard V' _ P' X' x' hX' hx'
    -- Handle trivial cases
    by_cases hX_singleton : ∀ y ∈ X', y = x'
    · -- X' = {x'}, so removeClonesExcept P' X' x' ≃ P'
      refine ⟨?_, ?_⟩
      · -- irv_nonclone_prop
        intro c hc
        -- Since hc : c ∉ X' and hX_singleton says X' = {x'}, we have c ≠ x'
        -- The restricted profile has the same candidates since only x' is in X'
        -- and x' is kept
        classical
        -- Every candidate satisfies the clone predicate when X' is a singleton.
        have hpred : ∀ a : A', clonePred X' x' a := by
          intro a
          by_cases hax : a = x'
          · subst hax
            exact Or.inr rfl
          · left
            intro haX
            exact hax (hX_singleton a haX)
        -- Equivalence between A' and the restricted candidate subtype.
        let e : A' ≃ {a : A' // clonePred X' x' a} :=
          { toFun := fun a => ⟨a, hpred a⟩
            invFun := fun s => (s : A')
            left_inv := by intro a; rfl
            right_inv := by intro s; ext; rfl }
        have hrelabel : relabelProfile P' e = removeClonesExcept P' X' x' := by
          ext v
          rfl
        -- Neutrality / equivariance of scoring elimination under relabeling.
        have heq' :
            scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') =
              (scoringEliminationAux pluralityScore A' P').map e.toEmbedding := by
          simpa [hrelabel] using
            (scoringEliminationAux_equiv (score := pluralityScore) (P := P') (e := e))
        have hmem :
            (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) ∈
                scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              c ∈ scoringEliminationAux pluralityScore A' P' := by
          -- Rewrite winners via `heq'` and use `mem_relabelWinners`.
          let b : {a : A' // clonePred X' x' a} := ⟨c, Or.inl hc⟩
          have hsymm : e.symm b = c := by rfl
          have hb0 : b ∈ (scoringEliminationAux pluralityScore A' P').map e.toEmbedding ↔
              e.symm b ∈ scoringEliminationAux pluralityScore A' P' :=
            mem_relabelWinners (e := e) (s := scoringEliminationAux pluralityScore A' P') (b := b)
          have hb : b ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              e.symm b ∈ scoringEliminationAux pluralityScore A' P' := by
            rw [heq']
            exact hb0
          have hb' : b ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              c ∈ scoringEliminationAux pluralityScore A' P' := by
            simpa [hsymm] using hb
          simpa [b] using hb'
        exact hmem.symm
      · -- irv_clone_prop
        -- (∃ y ∈ X', y wins) ↔ x' wins in restricted
        -- Since X' = {x'}, LHS is just (x' wins in P')
        classical
        -- Every candidate satisfies the clone predicate when X' is a singleton.
        have hpred : ∀ a : A', clonePred X' x' a := by
          intro a
          by_cases hax : a = x'
          · subst hax
            exact Or.inr rfl
          · left
            intro haX
            exact hax (hX_singleton a haX)
        let e : A' ≃ {a : A' // clonePred X' x' a} :=
          { toFun := fun a => ⟨a, hpred a⟩
            invFun := fun s => (s : A')
            left_inv := by intro a; rfl
            right_inv := by intro s; ext; rfl }
        have hrelabel : relabelProfile P' e = removeClonesExcept P' X' x' := by
          ext v
          rfl
        have heq' :
            scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') =
              (scoringEliminationAux pluralityScore A' P').map e.toEmbedding := by
          simpa [hrelabel] using
            (scoringEliminationAux_equiv (score := pluralityScore) (P := P') (e := e))
        have hxmem :
            (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ∈
                scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              x' ∈ scoringEliminationAux pluralityScore A' P' := by
          let b : {a : A' // clonePred X' x' a} := ⟨x', Or.inr rfl⟩
          have hsymm : e.symm b = x' := by rfl
          have hb0 : b ∈ (scoringEliminationAux pluralityScore A' P').map e.toEmbedding ↔
              e.symm b ∈ scoringEliminationAux pluralityScore A' P' :=
            mem_relabelWinners (e := e) (s := scoringEliminationAux pluralityScore A' P') (b := b)
          have hb : b ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              e.symm b ∈ scoringEliminationAux pluralityScore A' P' := by
            rw [heq']
            exact hb0
          have hb' : b ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              x' ∈ scoringEliminationAux pluralityScore A' P' := by
            simpa [hsymm] using hb
          simpa [b] using hb'
        -- Now convert between “some clone wins” and “x' wins” using singletonness.
        constructor
        · intro hex
          rcases hex with ⟨y, hyX, hywin⟩
          have hyEq : y = x' := hX_singleton y hyX
          subst hyEq
          exact (hxmem.mpr hywin)
        · intro hxwin
          refine ⟨x', hx', ?_⟩
          exact (hxmem.mp hxwin)
    · push_neg at hX_singleton
      -- There exists y ∈ X' with y ≠ x'
      rcases hX_singleton with ⟨y, hy, hyx⟩
      -- Check if all candidates are clones
      by_cases hX_all : X' = Set.univ
      · -- All candidates are clones
        -- removeClonesExcept P' X' x' has only x' as candidate
        -- scoringEliminationAux returns univ for 1-candidate elections
        refine ⟨?_, ?_⟩
        · intro c hc
          -- c ∉ X' = univ, contradiction
          exact (hc (hX_all ▸ Set.mem_univ c)).elim
        · -- (∃ y ∈ X', y wins) ↔ x' wins in restricted
          constructor
          · intro _
            -- x' wins in 1-candidate election (it's the only candidate)
            -- In 1-candidate case, univ is returned
            classical
            -- The restricted candidate type is a subsingleton when `X' = univ`.
            have hsub : Subsingleton {a : A' // clonePred X' x' a} := by
              refine ⟨?_⟩
              intro a b
              ext
              have ha : (a : A') = x' := by
                -- `a ∉ univ` is false, so the predicate forces `a = x'`.
                simpa [clonePred, hX_all] using a.property
              have hb : (b : A') = x' := by
                simpa [clonePred, hX_all] using b.property
              simp [ha, hb]
            have hcard_le : Fintype.card {a : A' // clonePred X' x' a} ≤ 1 :=
              Fintype.card_le_one_iff_subsingleton.2 hsub
            -- Base case of the elimination procedure.
            simp [scoringEliminationAux, hcard_le]
          · intro _
            -- Some clone wins in P' - in fact, all candidates win when there's 1+
            classical
            haveI : Nonempty A' := by
              -- `X' = univ` and `CloneSet` gives `X'.Nonempty`.
              rcases (by
                simpa [hX_all] using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
              exact ⟨a⟩
            rcases scoringEliminationAux_nonempty (score := pluralityScore) (P := P') with ⟨w, hw⟩
            refine ⟨w, ?_, hw⟩
            simp [hX_all]
      · push_neg at hX_all
        -- General case: use strong induction
        -- Unfold scoringEliminationAux and do case analysis
        by_cases hcard_le : Fintype.card A' ≤ 1
        · -- 0 or 1 candidates
          -- With ≤ 1 candidates and X' ⊂ A', X' must be empty, contradicting hX'.1
          rcases hX' with ⟨⟨z, hz⟩, _⟩
          have hne : ∃ w, w ∉ X' := by
            by_contra hall
            push_neg at hall
            have hXuniv : X' = Set.univ := Set.eq_univ_of_forall hall
            exact hX_all hXuniv
          rcases hne with ⟨w, hw⟩
          -- We have z ∈ X' and w ∉ X', so z ≠ w
          have hzw : z ≠ w := by
            intro hEq
            exact hw (hEq ▸ hz)
          -- But card A' ≤ 1 means all elements are equal
          have hsub : Subsingleton A' := Fintype.card_le_one_iff_subsingleton.1 hcard_le
          exact (hzw (Subsingleton.elim z w)).elim
        · push_neg at hcard_le
          -- Card > 1, so we can recurse
          refine ⟨?_, ?_⟩
          · -- irv_nonclone_prop
            intro c hc
            constructor
            · -- c ∈ winners(P') → c ∈ winners(P' - X' + x')
              intro hcwin
              -- Unfold one step of elimination
              have haux := scoringEliminationAux_eq_biUnion_of_not_card_le_one
                (score := pluralityScore) (P := P') (by omega : ¬ Fintype.card A' ≤ 1)
              rw [haux] at hcwin
              -- c is in biUnion, so there exists ℓ ∈ lowestScoring such that c ∈ winners(P'-ℓ)
              rcases Finset.mem_biUnion.mp hcwin with ⟨ℓ, hℓ_low, hc_rec⟩
              -- Case split on whether ℓ ∈ X'
              by_cases hℓX : ℓ ∈ X'
              · -- ℓ ∈ X': use IH on P'-ℓ with clone set X'\{ℓ}
                classical
                have hcnℓ : c ≠ ℓ := by
                  have :=
                    (liftFinset_subset_of_prop
                      (s := scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ))
                      c hc_rec)
                  simpa using this

                have hc_rec' : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                    scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                  rcases Finset.mem_image.mp hc_rec with ⟨d, hd, hdval⟩
                  have hd' : d = (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) := by
                    ext
                    simpa [liftFinset] using hdval
                  simpa [hd'] using hd

                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)

                by_cases hℓeq : ℓ = x'
                ·
                  -- Prefer eliminating `ℓ` (not `x'`) so we can keep using `x'` below.
                  have hx'ℓ : x' = ℓ := hℓeq.symm
                  subst hx'ℓ
                  -- Use the witness `y ∈ X'` with `y ≠ x'` from the outer scope.
                  let xℓ : {x : A' // x ≠ x'} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' x') (restrictCloneSet X' x') :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := x') (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' x' := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' x') (restrictCloneSet X' x') xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ x'}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ x'}) rfl (P' := restrictProfile P' x')
                      (X' := restrictCloneSet X' x') (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' x') (restrictCloneSet X' x') xℓ :=
                    hrecProps.1

                  have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ x'}) ∉ restrictCloneSet X' x' := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem

                  have hc_after_remove :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' x') (restrictCloneSet X' x') xℓ) := by
                    have := (hnon_restr (⟨c, hcnℓ⟩ : {x : A' // x ≠ x'}) hc_restr).mp hc_rec'
                    simpa using this

                  -- Rewrite the restricted collapse as a relabeling of the full collapse with rep `y`.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := x') (hℓ := hx') (hxℓ := hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩

                  have hbR' :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' y) e) := by
                    simpa [hcomm] using hc_after_remove

                  have heq :
                      scoringEliminationAux pluralityScore _
                          (relabelProfile (removeClonesExcept P' X' y) e) =
                        (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                          e.toEmbedding := by
                    simpa using
                      (scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' y) (e := e))

                  have hb_map :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                            e.toEmbedding := by
                    simpa [heq] using hbR'

                  have hb_pre :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) :=
                    (mem_relabelWinners (e := e)
                      (s := scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y))
                      (b := (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a}))).1 hb_map

                  have hb_val :
                      (e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩)).1 = c := by
                    -- `he_symm_val` gives the underlying value of the preimage.
                    simpa using (he_symm_val (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩))
                  have hb_val' :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩) =
                        (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) := by
                    apply Subtype.ext
                    simp [hb_val]
                  have hc_win_y :
                      (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    simpa [hb_val'] using hb_pre

                  -- Switch representative from `y` to `x'` (full collapse).
                  have hswapProf :
                      relabelProfile (removeClonesExcept P' X' y)
                          (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx)) =
                        removeClonesExcept P' X' x' :=
                    relabelProfile_removeClonesExcept_swap_rep
                      (P := P') (X := X') (x := y) (x' := x')
                      (hX := hX')
                      (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)

                  have hc_win_relabel :
                      (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))
                          (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                          (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx)).toEmbedding := by
                    exact Finset.mem_map_of_mem _ hc_win_y

                  -- Rewrite the target winners using `hswapProf` and equivariance.
                  have hswapW :=
                    scoringEliminationAux_equiv (score := pluralityScore)
                      (P := removeClonesExcept P' X' y)
                      (e := cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))
                  -- The mapped membership is precisely membership in the relabeled winners.
                  have hc_win_relabeled :
                      (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))
                          (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _
                          (relabelProfile (removeClonesExcept P' X' y)
                            (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))) := by
                    -- Use `hswapW` as a rewrite.
                    simpa [hswapW] using hc_win_relabel

                  -- Finally rewrite the profile to `removeClonesExcept P' X' x'`.
                  have hfix :=
                    cloneSwapEquiv_apply_nonclone (X := X') (x := y) (x' := x') (c := c)
                      (hc := hc) (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)
                  simpa [hswapProf, hfix] using hc_win_relabeled
                · -- `ℓ ≠ x'`: keep the same representative `x'` in the restricted election.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.1
                  have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem
                  have hc_after_remove :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    have := (hnon_restr (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) hc_restr).mp hc_rec'
                    simpa using this
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  have hbR' :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' x') e) := by
                    simpa [hcomm] using hc_after_remove
                  have heq :
                      scoringEliminationAux pluralityScore _
                          (relabelProfile (removeClonesExcept P' X' x') e) =
                        (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                          e.toEmbedding := by
                    simpa using
                      (scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' x') (e := e))
                  have hb_map :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                            e.toEmbedding := by
                    simpa [heq] using hbR'

                  have hb_pre :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') :=
                    (mem_relabelWinners (e := e)
                      (s := scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x'))
                      (b := (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}))).1 hb_map
                  have hb_val :
                      ((e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩)).1 : A') = c := by
                    simpa using (he_symm_val (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩))
                  have hb_val' :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩) =
                        (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hb_val]
                  simpa [hb_val'] using hb_pre
              · -- ℓ ∉ X': ℓ is also lowest in P'-X'+x', use IH on P'-ℓ with clone set X'
                classical
                have hℓnotX : ℓ ∉ X' := hℓX

                -- From `hc_rec : c ∈ liftFinset (...)`, we get `c ≠ ℓ` and the corresponding
                -- subtype winner in the restricted election.
                have hcnℓ : c ≠ ℓ := by
                  have :=
                    (liftFinset_subset_of_prop
                      (s := scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ))
                      c hc_rec)
                  simpa using this

                have hc_rec' : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                    scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                  -- `liftFinset` is `image Subtype.val`.
                  rcases Finset.mem_image.mp hc_rec with ⟨d, hd, hdval⟩
                  have hd' : d = (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) := by
                    ext
                    simpa [liftFinset] using hdval
                  simpa [hd'] using hd

                -- Apply IH to the restricted profile `P' - ℓ`.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  apply hℓnotX
                  simpa [hEq] using hx'
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  -- membership is by value
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  -- specialize IH
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hnon_restr :
                    irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.1

                have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                  intro hmem
                  apply hc
                  simpa [restrictCloneSet] using hmem

                have hc_after_remove :
                    (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                          (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  -- use the IH equivalence
                  have := (hnon_restr (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) hc_restr).mp hc_rec'
                  simpa using this

                -- Transport this recursive-winner fact to the clone-restricted election where
                -- `ℓ` is eliminated first.
                have hxℓ' : x' ≠ ℓ := hxne
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxℓ') (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩

                -- Unfold one step of elimination on the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 := by
                  -- There exists a non-clone candidate since `X' ≠ univ`.
                  have hne : ∃ w : A', w ∉ X' := by
                    by_contra hall
                    push_neg at hall
                    have hXuniv : X' = Set.univ := Set.eq_univ_of_forall hall
                    exact hX_all hXuniv
                  rcases hne with ⟨w, hw⟩
                  intro hle
                  have hsub : Subsingleton {a : A' // clonePred X' x' a} :=
                    Fintype.card_le_one_iff_subsingleton.1 hle
                  have hneq :
                      (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ≠
                        (⟨w, Or.inl hw⟩ : {a : A' // clonePred X' x' a}) := by
                    intro hEq
                    have hxw : x' = w := by
                      simpa using congrArg Subtype.val hEq
                    exact hw (hxw ▸ hx')
                  exact hneq (Subsingleton.elim _ _)

                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)

                -- Show membership in the RHS biUnion by choosing the elimination candidate `ℓ`.
                have hℓ_low' : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                  simpa [pluralityScore, pluralityScoreVec] using hℓ_low
                have hℓ_low_cl :
                    (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ∈
                      lowestScoring (removeClonesExcept P' X' x') pluralityScoreVec := by
                  exact
                    lowestScoring_nonclone_preserved (P := P') (X := X') (x := x')
                      (hX := hX') (hx := hx') (hℓ := hℓnotX) (hℓ_low := hℓ_low')

                -- It remains to show that `c` is a winner in the recursive call after eliminating `ℓ`.
                -- This follows by transporting `hc_after_remove` across `hcomm` and lifting.
                have hc_in_rec_cl :
                    (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) ∈
                      liftFinset
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))) := by
                  classical
                  -- Name the RHS winner element.
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    ⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩
                  have hbR :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [bR] using hc_after_remove

                  -- Rewrite the RHS profile using the commutation equality.
                  have hbR' :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                          e) := by
                    simpa [hcomm] using hbR

                  -- Use equivariance of `scoringEliminationAux` under relabeling.
                  have heq :
                      scoringEliminationAux pluralityScore _
                          (relabelProfile
                            (restrictProfile (removeClonesExcept P' X' x')
                              (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                            e) =
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                          e.toEmbedding := by
                    simpa using
                      (scoringEliminationAux_equiv (score := pluralityScore)
                        (P :=
                          restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                        (e := e))
                  have hb_map :
                      bR ∈
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                          e.toEmbedding := by
                    simpa [heq] using hbR'

                  have hb_pre :
                      e.symm bR ∈ scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a})) :=
                    (mem_relabelWinners (e := e)
                      (s :=
                        scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a})))
                      (b := bR)).1 hb_map

                  -- Show that the preimage winner has underlying value `c`.
                  have hb_val :
                      ((e.symm bR).1 : {a : A' // clonePred X' x' a}).1 = c := by
                    simpa [bR] using (he_symm_val bR)
                  have hb_val' :
                      e.symm bR =
                        (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hb_val]

                  -- Lift the winner back to the parent candidate type.
                  refine Finset.mem_image.mpr ?_
                  refine ⟨e.symm bR, hb_pre, ?_⟩
                  simp [hb_val']

                -- Combine everything to get membership in the clone-restricted winners.
                rw [haux_cl]
                refine Finset.mem_biUnion.mpr ?_
                refine ⟨(⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}), hℓ_low_cl, ?_⟩
                simpa [liftFinset] using hc_in_rec_cl
            · -- c ∈ winners(P' - X' + x') → c ∈ winners(P')
              intro hcwin
              classical
              -- Unfold one step of elimination in the original election.
              have haux_orig :=
                scoringEliminationAux_eq_biUnion_of_not_card_le_one
                  (score := pluralityScore) (P := P')
                  (by omega : ¬ Fintype.card A' ≤ 1)
              -- Case split: is some clone lowest-scoring in P'?
              by_cases hclone_low :
                  ∃ ℓ, ℓ ∈ lowestScoring P' pluralityScoreVec ∧ ℓ ∈ X'
              · -- There is a lowest-scoring clone in P'.
                rcases hclone_low with ⟨ℓ, hℓ_low, hℓX⟩
                have hcnℓ : c ≠ ℓ := by
                  intro hEq
                  exact hc (hEq ▸ hℓX)
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                by_cases hℓeq : ℓ = x'
                · -- ℓ is the representative: switch to y as rep.
                  subst hℓeq
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.1
                  have hc_restr :
                      (⟨c, by simpa using hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉
                        restrictCloneSet X' ℓ := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem
                  -- Switch representatives to y in the collapsed election.
                  have hcwin_y :
                      (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    have hswap :=
                      nonclone_winner_rep_independent (P := P') (X := X') (x := ℓ) (x' := y)
                        (c := c) (hc := hc) (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have hswapProf :=
                      relabelProfile_removeClonesExcept_swap_rep (P := P') (X := X') (x := ℓ) (x' := y)
                        (hX := hX') (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have := (hswap.mp hcwin)
                    simpa [hswapProf] using this
                  -- Commute restriction and clone removal.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := ℓ) (hℓ := hx')
                        (hxℓ := by simpa using hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hcwin_y
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' y) e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' y) (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = c := by
                    simpa [bR] using (he_val (⟨c, Or.inl hc⟩))
                  have hb_val' :
                      bR =
                        (⟨⟨c, by simpa using hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val]
                  have hc_after_remove :
                      (⟨⟨c, by simpa using hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hc_rec' :
                      (⟨c, by simpa using hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                        scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                    have := (hnon_restr (⟨c, by simpa using hcnℓ⟩) hc_restr).mpr hc_after_remove
                    simpa using this
                  have hc_rec :
                      c ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨(⟨c, by simpa using hcnℓ⟩ : {x : A' // x ≠ ℓ}), hc_rec', ?_⟩
                    simp
                  rw [haux_orig]
                  refine Finset.mem_biUnion.mpr ?_
                  refine ⟨ℓ, hℓ_low, ?_⟩
                  simpa using hc_rec
                · -- ℓ ≠ x': keep x' as the representative.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.1
                  have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hcwin
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' x') e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' x') (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = c := by
                    simpa [bR] using (he_val (⟨c, Or.inl hc⟩))
                  have hb_val' :
                      bR =
                        (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val]
                  have hc_after_remove :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hc_rec' :
                      (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                        scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                    have := (hnon_restr (⟨c, hcnℓ⟩) hc_restr).mpr hc_after_remove
                    simpa using this
                  have hc_rec :
                      c ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨(⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}), hc_rec', ?_⟩
                    simp
                  rw [haux_orig]
                  refine Finset.mem_biUnion.mpr ?_
                  refine ⟨ℓ, hℓ_low, ?_⟩
                  simpa using hc_rec
              · -- No clone is lowest-scoring in P'.
                -- Unfold one step of elimination in the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 := by
                  -- There exists a non-clone since X' ≠ univ.
                  have hne : ∃ w : A', w ∉ X' := by
                    by_contra hall
                    push_neg at hall
                    have hXuniv : X' = Set.univ := Set.eq_univ_of_forall hall
                    exact hX_all hXuniv
                  rcases hne with ⟨w, hw⟩
                  intro hle
                  have hsub : Subsingleton {a : A' // clonePred X' x' a} :=
                    Fintype.card_le_one_iff_subsingleton.1 hle
                  have hneq :
                      (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ≠
                        (⟨w, Or.inl hw⟩ : {a : A' // clonePred X' x' a}) := by
                    intro hEq
                    have hxw : x' = w := by
                      simpa using congrArg Subtype.val hEq
                    exact hw (hxw ▸ hx')
                  exact hneq (Subsingleton.elim _ _)
                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)
                -- Extract the elimination candidate from `hcwin`.
                have hcwin' := hcwin
                rw [haux_cl] at hcwin'
                rcases Finset.mem_biUnion.mp hcwin' with ⟨ℓ, hℓ_low_cl, hc_rec_cl⟩
                rcases ℓ with ⟨ℓ, hℓ_pred⟩
                -- Show that ℓ is a non-clone.
                have hℓnotX : ℓ ∉ X' := by
                  cases hℓ_pred with
                  | inl hℓnotX => exact hℓnotX
                  | inr hℓeq =>
                      subst hℓeq
                      -- If the representative is lowest in the collapsed election,
                      -- then some clone is lowest in P', contradicting `hclone_low`.
                      have hA : (Finset.univ : Finset A').Nonempty := by
                        rcases (by
                          simpa using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
                        haveI : Nonempty A' := ⟨a⟩
                        exact Finset.univ_nonempty
                      rcases lowestScoring_nonempty (P := P') (score := pluralityScoreVec) hA with ⟨w, hw⟩
                      by_cases hwX : w ∈ X'
                      · exact (hclone_low ⟨w, hw, hwX⟩).elim
                      · -- w is a non-clone. Show ℓ is also lowest.
                        have hrep_le_w_cl :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨w, Or.inl hwX⟩ : {a : A' // clonePred X' ℓ a}) :=
                          scoreCandidate_le_of_mem_lowestScoring
                            (P := removeClonesExcept P' X' ℓ) (score := pluralityScoreVec) (hc := hℓ_low_cl)
                        have hrep_le_w :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate P' pluralityScoreVec w := by
                          have hscore_w :=
                            score_nonclone_eq (P := P') (X := X') (x := ℓ)
                              (hX := hX') (hx := hx') (ha := hwX)
                          simpa [hscore_w] using hrep_le_w_cl
                        have hx_le_rep :
                            scoreCandidate P' pluralityScoreVec ℓ ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) :=
                          score_rep_ge_clone (P := P') (X := X') (x := ℓ) (y := ℓ)
                            (hX := hX') (hx := hx') (hy := hx')
                        have hx_le_w : scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec w :=
                          le_trans hx_le_rep hrep_le_w
                        have hw_le : ∀ d : A', scoreCandidate P' pluralityScoreVec w ≤ scoreCandidate P' pluralityScoreVec d := by
                          intro d
                          exact scoreCandidate_le_of_mem_lowestScoring
                            (P := P') (score := pluralityScoreVec) (hc := hw)
                        have hx_low : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                          apply (lowestScoring_iff_forall_le (P := P') (score := pluralityScoreVec) hA ℓ).2
                          intro d
                          exact le_trans hx_le_w (hw_le d)
                        exact (hclone_low ⟨ℓ, hx_low, hx'⟩).elim
                -- Extract the witness from the recursive winner in the collapsed election.
                rcases Finset.mem_image.mp hc_rec_cl with ⟨d, hd, hdval⟩
                have hcnℓ : c ≠ ℓ := by
                  intro hEq
                  have hEq' :
                      (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) =
                        (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) := by
                    ext
                    simp [hEq]
                  have : d.1 = (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) := by
                    simpa [hdval] using hEq'
                  exact d.property this
                -- Apply IH to the restricted profile.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  exact hℓnotX (hEq ▸ hx')
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hnon_restr :
                    irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.1
                have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                  intro hmem
                  apply hc
                  simpa [restrictCloneSet] using hmem
                -- Transport membership across the commutation lemma.
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxne) (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩
                let bR :
                    {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                  e d
                have hb_map :
                    bR ∈ (scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                      e.toEmbedding := by
                  exact Finset.mem_map_of_mem _ hd
                have hb_relabel :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (relabelProfile
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                        e) := by
                  have heq :=
                    scoringEliminationAux_equiv (score := pluralityScore)
                      (P :=
                        restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                      (e := e)
                  simpa [heq] using hb_map
                have hb_after :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hcomm] using hb_relabel
                have hb_val :
                    ((bR).1 : {x : A' // x ≠ ℓ}).1 = c := by
                  simpa [bR, hdval] using (he_val d)
                have hb_val' :
                    bR =
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                  apply Subtype.ext
                  ext
                  simp [hb_val]
                have hc_after_remove :
                    (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hb_val'] using hb_after
                have hc_rec'' :
                    (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                      scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                  have := (hnon_restr (⟨c, hcnℓ⟩) hc_restr).mpr hc_after_remove
                  simpa using this
                have hc_rec :
                    c ∈
                      liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ)) := by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨(⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}), hc_rec'', ?_⟩
                  simp
                -- Show ℓ is lowest-scoring in P' (clones are not lowest).
                have hA : (Finset.univ : Finset A').Nonempty := by
                  rcases (by
                    simpa using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
                  haveI : Nonempty A' := ⟨a⟩
                  exact Finset.univ_nonempty
                have hℓ_low' :
                    ℓ ∈ lowestScoring P' pluralityScoreVec := by
                  apply (lowestScoring_iff_forall_le (P := P') (score := pluralityScoreVec) hA ℓ).2
                  intro d
                  by_cases hdX : d ∈ X'
                  · -- If a clone were lower, it would contradict `hclone_low`.
                    by_contra hlt
                    have hlt' : scoreCandidate P' pluralityScoreVec d < scoreCandidate P' pluralityScoreVec ℓ :=
                      lt_of_not_ge hlt
                    -- Any non-clone has score ≥ ℓ (from collapsed lowest).
                    have hℓ_le_nonclone :
                        ∀ a : A', a ∉ X' →
                          scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec a := by
                      intro a haX
                      have hℓ_le_a_cl :
                          scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                              (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ≤
                            scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                              (⟨a, Or.inl haX⟩ : {a : A' // clonePred X' x' a}) :=
                        scoreCandidate_le_of_mem_lowestScoring
                          (P := removeClonesExcept P' X' x') (score := pluralityScoreVec) (hc := hℓ_low_cl)
                      have hscore_a :=
                        score_nonclone_eq (P := P') (X := X') (x := x')
                          (hX := hX') (hx := hx') (ha := haX)
                      have hscore_ℓ :=
                        score_nonclone_eq (P := P') (X := X') (x := x')
                          (hX := hX') (hx := hx') (ha := hℓnotX)
                      -- Rewrite both sides to original scores.
                      simpa [hscore_a, hscore_ℓ] using hℓ_le_a_cl
                    -- Choose any non-clone a (exists since X' ≠ univ).
                    -- Pick a lowest-scoring candidate `w`.
                    rcases lowestScoring_nonempty (P := P') (score := pluralityScoreVec) hA with ⟨w, hw⟩
                    by_cases hwX : w ∈ X'
                    · exact (hclone_low ⟨w, hw, hwX⟩).elim
                    · -- `w` is a non-clone, hence its score is ≥ ℓ, contradicting `d < ℓ`.
                      have hℓ_le_w := hℓ_le_nonclone w hwX
                      have hw_le_d :
                          scoreCandidate P' pluralityScoreVec w ≤ scoreCandidate P' pluralityScoreVec d :=
                        scoreCandidate_le_of_mem_lowestScoring
                          (P := P') (score := pluralityScoreVec) (hc := hw)
                      have hℓ_le_d : scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec d :=
                        le_trans hℓ_le_w hw_le_d
                      have hcontra :
                          scoreCandidate P' pluralityScoreVec d < scoreCandidate P' pluralityScoreVec d :=
                        lt_of_lt_of_le hlt' hℓ_le_d
                      exact (lt_irrefl _ hcontra).elim
                  · -- d is a non-clone: use preservation of scores.
                    have hℓ_le_d_cl :
                        scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ≤
                          scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                            (⟨d, Or.inl hdX⟩ : {a : A' // clonePred X' x' a}) :=
                      scoreCandidate_le_of_mem_lowestScoring
                        (P := removeClonesExcept P' X' x') (score := pluralityScoreVec) (hc := hℓ_low_cl)
                    have hscore_d :=
                      score_nonclone_eq (P := P') (X := X') (x := x')
                        (hX := hX') (hx := hx') (ha := hdX)
                    have hscore_ℓ :=
                      score_nonclone_eq (P := P') (X := X') (x := x')
                        (hX := hX') (hx := hx') (ha := hℓnotX)
                    simpa [hscore_d, hscore_ℓ] using hℓ_le_d_cl
                -- Conclude in the original election.
                rw [haux_orig]
                refine Finset.mem_biUnion.mpr ?_
                refine ⟨ℓ, hℓ_low', ?_⟩
                simpa using hc_rec
          · -- irv_clone_prop
            constructor
            · -- (∃ y ∈ X', y wins in P') → x' wins in P'-X'+x'
              intro ⟨w, hw, hwwin⟩
              classical
              -- Unfold one step of elimination in the original election.
              have haux :=
                scoringEliminationAux_eq_biUnion_of_not_card_le_one
                  (score := pluralityScore) (P := P') (by omega : ¬ Fintype.card A' ≤ 1)
              rw [haux] at hwwin
              rcases Finset.mem_biUnion.mp hwwin with ⟨ℓ, hℓ_low, hw_rec⟩
              -- Extract `w ≠ ℓ` and the recursive winner.
              have hwnℓ : w ≠ ℓ := by
                have :=
                  (liftFinset_subset_of_prop
                    (s := scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                      (restrictProfile P' ℓ))
                    w hw_rec)
                simpa using this
              have hw_rec' : (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                  scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                rcases Finset.mem_image.mp hw_rec with ⟨d, hd, hdval⟩
                have hd' : d = (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) := by
                  ext
                  simpa [liftFinset] using hdval
                simpa [hd'] using hd
              by_cases hℓX : ℓ ∈ X'
              · -- ℓ is a clone: use IH on the restricted profile.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                by_cases hℓeq : ℓ = x'
                ·
                  -- ℓ is the representative: switch to `y`.
                  subst hℓeq
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  have hw_restr_mem :
                      (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet] using hw
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    exact (hclone_restr.mp ⟨⟨w, hwnℓ⟩, hw_restr_mem, hw_rec'⟩)
                  -- Transport to the full collapse with representative `y`.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := ℓ) (hℓ := hx')
                        (hxℓ := by simpa using hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  have hxℓ_win' :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' y) e) := by
                    simpa [hcomm] using hxℓ_win
                  have heq :
                      scoringEliminationAux pluralityScore _
                          (relabelProfile (removeClonesExcept P' X' y) e) =
                        (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                          e.toEmbedding := by
                    simpa using
                      (scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' y) (e := e))
                  have hxℓ_map :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                          e.toEmbedding := by
                    simpa [heq] using hxℓ_win'
                  have hxℓ_pre :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) :=
                    (mem_relabelWinners (e := e)
                      (s := scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y))
                      (b := (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}))).1
                      hxℓ_map
                  have hxℓ_val :
                      (e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})).1 = y := by
                    simpa [xℓ] using (he_symm_val (⟨xℓ, Or.inr rfl⟩))
                  have hxℓ_val' :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) =
                        (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a}) := by
                    apply Subtype.ext
                    simp [hxℓ_val]
                  have hy_win :
                      (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    simpa [hxℓ_val'] using hxℓ_pre
                  -- Switch representative from `y` back to `x'`.
                  have hswap :=
                    clone_winner_rep_independent (P := P') (X := X') (x := y) (x' := ℓ)
                      (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)
                  have hswapProf :=
                    relabelProfile_removeClonesExcept_swap_rep (P := P') (X := X') (x := y) (x' := ℓ)
                      (hX := hX') (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)
                  have := (hswap.mp hy_win)
                  simpa [hswapProf] using this
                · -- ℓ ≠ x': keep x' as the representative.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  have hw_restr_mem :
                      (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet] using hw
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    exact (hclone_restr.mp ⟨⟨w, hwnℓ⟩, hw_restr_mem, hw_rec'⟩)
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  have hxℓ_win' :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' x') e) := by
                    simpa [hcomm] using hxℓ_win
                  have heq :
                      scoringEliminationAux pluralityScore _
                          (relabelProfile (removeClonesExcept P' X' x') e) =
                        (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                          e.toEmbedding := by
                    simpa using
                      (scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' x') (e := e))
                  have hxℓ_map :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                            e.toEmbedding := by
                    simpa [heq] using hxℓ_win'
                  have hxℓ_pre :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') :=
                    (mem_relabelWinners (e := e)
                      (s := scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x'))
                      (b := (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}))).1
                      hxℓ_map
                  have hxℓ_val :
                      ((e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})).1 : A') = x' := by
                    simpa [xℓ] using (he_symm_val (⟨xℓ, Or.inr rfl⟩))
                  have hxℓ_val' :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) =
                        (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hxℓ_val]
                  simpa [hxℓ_val'] using hxℓ_pre
              · -- ℓ is a non-clone: use IH on P' - ℓ and lift to the full collapse.
                classical
                have hℓnotX : ℓ ∉ X' := hℓX
                -- Apply IH to the restricted profile `P' - ℓ`.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  apply hℓnotX
                  simpa [hEq] using hx'
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hclone_restr :
                    irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.2
                have hw_restr_mem : (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet] using hw
                have hxℓ_win :
                    (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                          (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  exact (hclone_restr.mp ⟨⟨w, hwnℓ⟩, hw_restr_mem, hw_rec'⟩)
                -- Transport to the clone-restricted election where `ℓ` is eliminated first.
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxne) (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩
                have hx_in_rec_cl :
                    (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ∈
                      liftFinset
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))) := by
                  classical
                  let bR :
                      {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    ⟨xℓ, Or.inr rfl⟩
                  have hbR :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [bR] using hxℓ_win
                  have hbR' :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                          e) := by
                    simpa [hcomm] using hbR
                  have heq :
                      scoringEliminationAux pluralityScore _
                          (relabelProfile
                            (restrictProfile (removeClonesExcept P' X' x')
                              (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                            e) =
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                          e.toEmbedding := by
                    simpa using
                      (scoringEliminationAux_equiv (score := pluralityScore)
                        (P :=
                          restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                        (e := e))
                  have hb_map :
                      bR ∈
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                          e.toEmbedding := by
                    simpa [heq] using hbR'
                  have hb_pre :
                      e.symm bR ∈ scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a})) :=
                    (mem_relabelWinners (e := e)
                      (s :=
                        scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a})))
                      (b := bR)).1 hb_map
                  have hb_val :
                      ((e.symm bR).1 : {a : A' // clonePred X' x' a}).1 = x' := by
                    simpa [bR, xℓ] using (he_symm_val bR)
                  have hb_val' :
                      e.symm bR =
                        (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hb_val]
                  refine Finset.mem_image.mpr ?_
                  refine ⟨e.symm bR, hb_pre, ?_⟩
                  simp [hb_val']
                -- Unfold one step of elimination on the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 := by
                  -- There exists a non-clone candidate since `X' ≠ univ`.
                  have hne : ∃ w : A', w ∉ X' := by
                    by_contra hall
                    push_neg at hall
                    have hXuniv : X' = Set.univ := Set.eq_univ_of_forall hall
                    exact hX_all hXuniv
                  rcases hne with ⟨w, hw'⟩
                  intro hle
                  have hsub : Subsingleton {a : A' // clonePred X' x' a} :=
                    Fintype.card_le_one_iff_subsingleton.1 hle
                  have hneq :
                      (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ≠
                        (⟨w, Or.inl hw'⟩ : {a : A' // clonePred X' x' a}) := by
                    intro hEq
                    have hxw : x' = w := by
                      simpa using congrArg Subtype.val hEq
                    exact hw' (hxw ▸ hx')
                  exact hneq (Subsingleton.elim _ _)
                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)
                have hℓ_low' : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                  simpa [pluralityScore, pluralityScoreVec] using hℓ_low
                have hℓ_low_cl :
                    (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ∈
                      lowestScoring (removeClonesExcept P' X' x') pluralityScoreVec := by
                  exact
                    lowestScoring_nonclone_preserved (P := P') (X := X') (x := x')
                      (hX := hX') (hx := hx') (hℓ := hℓnotX) (hℓ_low := hℓ_low')
                -- Conclude in the clone-restricted election.
                rw [haux_cl]
                refine Finset.mem_biUnion.mpr ?_
                refine ⟨(⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}), hℓ_low_cl, ?_⟩
                simpa [liftFinset] using hx_in_rec_cl
            · -- x' wins in P'-X'+x' → (∃ y ∈ X', y wins in P')
              intro hxwin
              classical
              -- Unfold one step of elimination in the original election.
              have haux_orig :=
                scoringEliminationAux_eq_biUnion_of_not_card_le_one
                  (score := pluralityScore) (P := P')
                  (by omega : ¬ Fintype.card A' ≤ 1)
              -- Case split: is some clone lowest-scoring in P'?
              by_cases hclone_low :
                  ∃ ℓ, ℓ ∈ lowestScoring P' pluralityScoreVec ∧ ℓ ∈ X'
              · -- There is a lowest-scoring clone in P'.
                rcases hclone_low with ⟨ℓ, hℓ_low, hℓX⟩
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                by_cases hℓeq : ℓ = x'
                · -- ℓ is the representative: switch to y as rep.
                  subst hℓeq
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  -- Switch representatives to y in the collapsed election.
                  have hxwin_y :
                      (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    have hswap :=
                      clone_winner_rep_independent (P := P') (X := X') (x := ℓ) (x' := y)
                        (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have hswapProf :=
                      relabelProfile_removeClonesExcept_swap_rep (P := P') (X := X') (x := ℓ) (x' := y)
                        (hX := hX') (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have := (hswap.mp hxwin)
                    simpa [hswapProf] using this
                  -- Commute restriction and clone removal.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := ℓ) (hℓ := hx')
                        (hxℓ := by simpa using hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hxwin_y
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' y) e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' y) (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = y := by
                    simpa [bR] using (he_val (⟨y, Or.inr rfl⟩))
                  have hb_val' :
                      bR =
                        (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val, xℓ]
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hxw_restr :
                      ∃ z, z ∈ restrictCloneSet X' ℓ ∧
                        z ∈ scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) :=
                    (hclone_restr.mpr hxℓ_win)
                  rcases hxw_restr with ⟨z, hzmem, hzwins⟩
                  have hz_inX : (z : A') ∈ X' := by
                    simpa [restrictCloneSet] using hzmem
                  have hz_lift :
                      (z : A') ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨z, hzwins, ?_⟩
                    simp
                  have hz_win : (z : A') ∈ scoringEliminationAux pluralityScore A' P' := by
                    rw [haux_orig]
                    refine Finset.mem_biUnion.mpr ?_
                    refine ⟨ℓ, hℓ_low, ?_⟩
                    simpa using hz_lift
                  exact ⟨(z : A'), hz_inX, hz_win⟩
                · -- ℓ ≠ x': keep x' as the representative.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hxwin
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' x') e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' x') (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = x' := by
                    simpa [bR] using (he_val (⟨x', Or.inr rfl⟩))
                  have hb_val' :
                      bR =
                        (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val, xℓ]
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hxw_restr :
                      ∃ z, z ∈ restrictCloneSet X' ℓ ∧
                        z ∈ scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) :=
                    (hclone_restr.mpr hxℓ_win)
                  rcases hxw_restr with ⟨z, hzmem, hzwins⟩
                  have hz_inX : (z : A') ∈ X' := by
                    simpa [restrictCloneSet] using hzmem
                  have hz_lift :
                      (z : A') ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨z, hzwins, ?_⟩
                    simp
                  have hz_win : (z : A') ∈ scoringEliminationAux pluralityScore A' P' := by
                    rw [haux_orig]
                    refine Finset.mem_biUnion.mpr ?_
                    refine ⟨ℓ, hℓ_low, ?_⟩
                    simpa using hz_lift
                  exact ⟨(z : A'), hz_inX, hz_win⟩
              · -- No clone is lowest-scoring in P'.
                -- Unfold one step of elimination in the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 := by
                  -- There exists a non-clone since X' ≠ univ.
                  have hne : ∃ w : A', w ∉ X' := by
                    by_contra hall
                    push_neg at hall
                    have hXuniv : X' = Set.univ := Set.eq_univ_of_forall hall
                    exact hX_all hXuniv
                  rcases hne with ⟨w, hw⟩
                  intro hle
                  have hsub : Subsingleton {a : A' // clonePred X' x' a} :=
                    Fintype.card_le_one_iff_subsingleton.1 hle
                  have hneq :
                      (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ≠
                        (⟨w, Or.inl hw⟩ : {a : A' // clonePred X' x' a}) := by
                    intro hEq
                    have hxw : x' = w := by
                      simpa using congrArg Subtype.val hEq
                    exact hw (hxw ▸ hx')
                  exact hneq (Subsingleton.elim _ _)
                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)
                -- Extract the elimination candidate from `hxwin`.
                have hxwin' := hxwin
                rw [haux_cl] at hxwin'
                rcases Finset.mem_biUnion.mp hxwin' with ⟨ℓ, hℓ_low_cl, hx_rec_cl⟩
                rcases ℓ with ⟨ℓ, hℓ_pred⟩
                -- Show that ℓ is a non-clone.
                have hℓnotX : ℓ ∉ X' := by
                  cases hℓ_pred with
                  | inl hℓnotX => exact hℓnotX
                  | inr hℓeq =>
                      subst hℓeq
                      -- If the representative is lowest in the collapsed election,
                      -- then some clone is lowest in P', contradicting `hclone_low`.
                      have hA : (Finset.univ : Finset A').Nonempty := by
                        rcases (by
                          simpa using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
                        haveI : Nonempty A' := ⟨a⟩
                        exact Finset.univ_nonempty
                      rcases lowestScoring_nonempty (P := P') (score := pluralityScoreVec) hA with ⟨w, hw⟩
                      by_cases hwX : w ∈ X'
                      · exact (hclone_low ⟨w, hw, hwX⟩).elim
                      · -- w is a non-clone. Show ℓ is also lowest.
                        have hrep_le_w_cl :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨w, Or.inl hwX⟩ : {a : A' // clonePred X' ℓ a}) :=
                          scoreCandidate_le_of_mem_lowestScoring
                            (P := removeClonesExcept P' X' ℓ) (score := pluralityScoreVec) (hc := hℓ_low_cl)
                        have hrep_le_w :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate P' pluralityScoreVec w := by
                          have hscore_w :=
                            score_nonclone_eq (P := P') (X := X') (x := ℓ)
                              (hX := hX') (hx := hx') (ha := hwX)
                          simpa [hscore_w] using hrep_le_w_cl
                        have hx_le_rep :
                            scoreCandidate P' pluralityScoreVec ℓ ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) :=
                          score_rep_ge_clone (P := P') (X := X') (x := ℓ) (y := ℓ)
                            (hX := hX') (hx := hx') (hy := hx')
                        have hx_le_w : scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec w :=
                          le_trans hx_le_rep hrep_le_w
                        have hw_le : ∀ d : A', scoreCandidate P' pluralityScoreVec w ≤ scoreCandidate P' pluralityScoreVec d := by
                          intro d
                          exact scoreCandidate_le_of_mem_lowestScoring
                            (P := P') (score := pluralityScoreVec) (hc := hw)
                        have hx_low : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                          apply (lowestScoring_iff_forall_le (P := P') (score := pluralityScoreVec) hA ℓ).2
                          intro d
                          exact le_trans hx_le_w (hw_le d)
                        exact (hclone_low ⟨ℓ, hx_low, hx'⟩).elim
                -- Extract the witness from the recursive winner in the collapsed election.
                rcases Finset.mem_image.mp hx_rec_cl with ⟨d, hd, hdval⟩
                have hd' :
                    d.1 = (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
                  simpa [liftFinset] using hdval
                -- Apply IH to the restricted profile.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  exact hℓnotX (hEq ▸ hx')
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hclone_restr :
                    irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.2
                -- Transport membership across the commutation lemma.
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxne) (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩
                let bR :
                    {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                  e d
                have hb_map :
                    bR ∈ (scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                      e.toEmbedding := by
                  exact Finset.mem_map_of_mem _ hd
                have hb_relabel :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (relabelProfile
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                        e) := by
                  have heq :=
                    scoringEliminationAux_equiv (score := pluralityScore)
                      (P :=
                        restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                      (e := e)
                  simpa [heq] using hb_map
                have hb_after :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hcomm] using hb_relabel
                have hb_val :
                    ((bR).1 : {x : A' // x ≠ ℓ}).1 = x' := by
                  simpa [bR, hd'] using (he_val d)
                have hb_val' :
                    bR =
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                  apply Subtype.ext
                  ext
                  simp [hb_val, xℓ]
                have hxℓ_win :
                    (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hb_val'] using hb_after
                have hxw_restr :
                    ∃ z, z ∈ restrictCloneSet X' ℓ ∧
                      z ∈ scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) :=
                  (hclone_restr.mpr hxℓ_win)
                rcases hxw_restr with ⟨z, hzmem, hzwins⟩
                have hz_inX : (z : A') ∈ X' := by
                  simpa [restrictCloneSet] using hzmem
                have hz_lift :
                    (z : A') ∈
                      liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ)) := by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨z, hzwins, ?_⟩
                  simp
                -- Show ℓ is lowest-scoring in P' (clones are not lowest).
                have hA : (Finset.univ : Finset A').Nonempty := by
                  rcases (by
                    simpa using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
                  haveI : Nonempty A' := ⟨a⟩
                  exact Finset.univ_nonempty
                have hℓ_low' :
                    ℓ ∈ lowestScoring P' pluralityScoreVec := by
                  apply (lowestScoring_iff_forall_le (P := P') (score := pluralityScoreVec) hA ℓ).2
                  intro d
                  by_cases hdX : d ∈ X'
                  · -- If a clone were lower, it would contradict `hclone_low`.
                    by_contra hlt
                    have hlt' : scoreCandidate P' pluralityScoreVec d < scoreCandidate P' pluralityScoreVec ℓ :=
                      lt_of_not_ge hlt
                    -- Any non-clone has score ≥ ℓ (from collapsed lowest).
                    have hℓ_le_nonclone :
                        ∀ a : A', a ∉ X' →
                          scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec a := by
                      intro a haX
                      have hℓ_le_a_cl :
                          scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                              (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ≤
                            scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                              (⟨a, Or.inl haX⟩ : {a : A' // clonePred X' x' a}) :=
                        scoreCandidate_le_of_mem_lowestScoring
                          (P := removeClonesExcept P' X' x') (score := pluralityScoreVec) (hc := hℓ_low_cl)
                      have hscore_a :=
                        score_nonclone_eq (P := P') (X := X') (x := x')
                          (hX := hX') (hx := hx') (ha := haX)
                      have hscore_ℓ :=
                        score_nonclone_eq (P := P') (X := X') (x := x')
                          (hX := hX') (hx := hx') (ha := hℓnotX)
                      -- Rewrite both sides to original scores.
                      simpa [hscore_a, hscore_ℓ] using hℓ_le_a_cl
                    -- Choose any non-clone a (exists since X' ≠ univ).
                    -- Pick a lowest-scoring candidate `w`.
                    rcases lowestScoring_nonempty (P := P') (score := pluralityScoreVec) hA with ⟨w, hw⟩
                    by_cases hwX : w ∈ X'
                    · exact (hclone_low ⟨w, hw, hwX⟩).elim
                    · -- `w` is a non-clone, hence its score is ≥ ℓ, contradicting `d < ℓ`.
                      have hℓ_le_w := hℓ_le_nonclone w hwX
                      have hw_le_d :
                          scoreCandidate P' pluralityScoreVec w ≤ scoreCandidate P' pluralityScoreVec d :=
                        scoreCandidate_le_of_mem_lowestScoring
                          (P := P') (score := pluralityScoreVec) (hc := hw)
                      have hℓ_le_d : scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec d :=
                        le_trans hℓ_le_w hw_le_d
                      have hcontra :
                          scoreCandidate P' pluralityScoreVec d < scoreCandidate P' pluralityScoreVec d :=
                        lt_of_lt_of_le hlt' hℓ_le_d
                      exact (lt_irrefl _ hcontra).elim
                  · -- d is a non-clone: use preservation of scores.
                    have hℓ_le_d_cl :
                        scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ≤
                          scoreCandidate (removeClonesExcept P' X' x') pluralityScoreVec
                            (⟨d, Or.inl hdX⟩ : {a : A' // clonePred X' x' a}) :=
                      scoreCandidate_le_of_mem_lowestScoring
                        (P := removeClonesExcept P' X' x') (score := pluralityScoreVec) (hc := hℓ_low_cl)
                    have hscore_d :=
                      score_nonclone_eq (P := P') (X := X') (x := x')
                        (hX := hX') (hx := hx') (ha := hdX)
                    have hscore_ℓ :=
                      score_nonclone_eq (P := P') (X := X') (x := x')
                        (hX := hX') (hx := hx') (ha := hℓnotX)
                    simpa [hscore_d, hscore_ℓ] using hℓ_le_d_cl
                -- Conclude in the original election.
                have hz_win : (z : A') ∈ scoringEliminationAux pluralityScore A' P' := by
                  rw [haux_orig]
                  refine Finset.mem_biUnion.mpr ?_
                  refine ⟨ℓ, hℓ_low', ?_⟩
                  simpa using hz_lift
                exact ⟨(z : A'), hz_inX, hz_win⟩
  -- Apply the strong induction result
  have h := @hStrong A instA (Classical.decEq _) rfl V instV P₀ X x hX hx
  simp only [clone_independence_props, irv_nonclone_prop, irv_clone_prop] at h
  -- Align the goal with the statement proven by `h`.
  simpa [scoringEliminationRule] using h

end SocialChoice
