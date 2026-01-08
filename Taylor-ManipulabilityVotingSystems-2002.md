Excerpt from "Taylor, Alan D. “The Manipulability of Voting Systems.” The American Mathematical Monthly, vol. 109, no. 4, 2002, pp. 321–37"

# 2. THE DUGGAN-SCHWARTZ THEOREM

As a context for a basic version of the Duggan-Schwartz Theorem, we take elections in which we have linear ballots, three or more alternatives, and in which the outcome of an election is—in contrast to what one has with the Gibbard-Satterthwaite Theorem—a non-empty set of winners. The kind of manipulation that we explore here is given by the following.

**Definition 2.1.** A voting system can be *manipulated by an optimistic voter* if there exists a profile $\langle B_1, \dots, B_n \rangle$ (which we think of as giving the true preferences of the $n$ voters) and another ballot $C_i$ (which we think of as a disingenuous ballot from voter $i$) such that at least one of the winners from the profile
$$\langle B_1, \dots, B_{i-1}, C_i, B_{i+1}, \dots, B_n \rangle$$
is—according to $B_i$—preferred to the all of the winners from $\langle B_1, \dots, B_n \rangle$. Similarly, a voting system can be *manipulated by a pessimistic voter* if there exists a profile $\langle B_1, \dots, B_n \rangle$ (which we think of as giving the true preferences of the $n$ voters) and another ballot $C_i$ (which we think of as a disingenuous ballot from voter $i$) such that all of the winners from the profile
$$\langle B_1, \dots, B_{i-1}, C_i, B_{i+1}, \dots, B_n \rangle$$
are—according to $B_i$—preferred to at least one of the winners from $\langle B_1, \dots, B_n \rangle$.

More briefly, a voting system can be manipulated by an optimist if there is at least one election in which some voter can file a disingenuous ballot and improve the max of the set of winners according to his true preferences. Similarly, a voting system can be manipulated by a pessimist if there is at least one election in which some voter can file a disingenuous ballot and improve the min of the set of winners according to his true preferences.

For the remainder of this section, we fix a context in which there are three or more alternatives, $n$ voters for some fixed $n$, linear ballots (ties in the ballots are handled later), and—with the exception of Corollary 2.13—elections in which the outcome is a non-empty set of winners. If $V$ is a voting system in this context, we say that an alternative $x$ is *viable* if $V(P) = \{x\}$ for at least one profile $P$.

**Theorem 2.2 (Duggan-Schwartz [9]).** *If $V$ is a voting system that cannot be manipulated by an optimist or a pessimist and in which every alternative $x$ is viable, then there exists at least one voter whose top choice is always among the set of winners.*

First, a piece of terminology: if $P$ is a profile, then a set $X$ of alternatives is said to be a *top set* (for $P$) if each voter prefers (according to his ballot) every alternative in $X$ to every alternative not in $X$. For example, if every voter has $x$ at the top of his ballot, then $\{x\}$ is a top set.

Suppose now that $V$ is a voting system that cannot be manipulated by an optimist or a pessimist, and that $P$ is a profile for which $X$ is a top set. Assume that there is at least one profile $P'$ for which $V(P') \subseteq X$. Then we claim that $V(P) \subseteq X$. If not, we could convert $P$ to $P'$, one ballot at a time, until the set of winners changes from not being a subset of $X$ (which we are assuming is true with $P$) to being a subset of $X$ (which we are assuming is true with $P'$). If this occurs as we change ballot $B_i$ to $C_i$, then we can take $B_i$ to be the true preferences of voter $i$ and see that his insincere submission of $C_i$ has improved the min (from something not in $X$ to something in $X$). This proves the claim.

The key to our proof of the Duggan-Schwartz Theorem is the following definition.

**Definition 2.3.** A voting system $V$ is said to satisfy *down-monotonicity for singleton winners* provided that the following always holds: if $P$ is a profile and $|V(P)| = 1$, and if $P'$ is the profile obtained from $P$ by having one voter move one losing alternative down one spot on his ballot, then $V(P') = V(P)$.

From down-monotonicity for singleton winners, it follows that, if the outcome of an election is a singleton, then that outcome is unchanged if any number of voters move any number of losing alternatives down any number of spots on their ballots.

**Lemma 2.4.** *If a voting system cannot be manipulated by an optimist or a pessimist, then it satisfies down-monotonicity for singleton winners.*

*Proof.* If down-monotonicity for singleton winners fails, then there exist two elections, a single voter $i$, and two alternatives $x$ and $y$ such that:

In Election #1, voter $i$ has ballot $B_i = \langle \dots y, x \dots \rangle$, and some $w \neq y$ is the only winner (that is, $y$ is a non-winner).

In Election #2, voter $i$ has ballot $C_i = \langle \dots x, y \dots \rangle$, all other ballots are the same as in Election #1, and some $Y \neq \{w\}$ is the set of winners.

Choose $v \in Y$ such that $v \neq w$. If $v$ is preferred to $w$ on both ballots, then we can regard $B_i$ as the true preferences, and see that voter $i$'s disingenuous submission of $C_i$ improves the max (according to his true preferences) from $w$ to at least $v$.

Similarly, if $w$ is preferred to $v$ on both ballots, then we can regard $C_i$ as the true preferences, and see that voter $i$'s disingenuous submission of $B_i$ improves the min (according to his true preferences) from $v$ or worse to $w$.

In the only remaining case, we must have $\{v, w\} = \{x, y\}$, and since $w \neq y$, we must have $x = w$ and $y = v$. But then we can regard $B_i$ as the true preferences, and see that voter $i$'s disingenuous submission of $C_i$ improves the max (according to his true preferences) from $x = w$ to at least $y = v$. We could also have regarded $C_i$ as the true preferences, and had voter $i$ improve the min. $\blacksquare$

**Definition 2.5.** If $V$ is a voting system, $X$ is a set of voters, and $a$ and $b$ are distinct alternatives, then we write "$a X b$" to mean that $V(P) \neq \{b\}$ whenever $P$ is a profile in which everyone in $X$ has $a$ over $b$ on his ballot. We say that $X$ is a *dictating set* if $a X b$ for every pair of distinct alternatives $a$ and $b$.

We really should include the name of the voting system $V$ in the notation "$a X b$" and similarly speak of a "dictating set for $V$", but our suppression of the name $V$ causes no confusion.

**Lemma 2.6.** *Assume that $V$ is a voting system that satisfies down-monotonicity for singleton winners. Then, in order to show that $a X b$, it suffices to find a single profile $P$ in which $\{a, b\}$ is a top set, everyone in $X$ prefers $a$ to $b$, everyone else prefers $b$ to $a$, and in which $a \in V(P)$.*

*Proof.* Assume that $a X b$ fails, and choose a profile $P'$ in which everyone in $X$ prefers $a$ to $b$ and for which $V(P') = \{b\}$. Using down-monotonicity for singleton winners, we can convert $P'$ into the profile $P$ that is assumed to exist, and get $V(P) = \{b\}$. But this is a contradiction since $a \in V(P)$. $\blacksquare$

**Lemma 2.7.** *Assume that $V$ is a voting system that satisfies down-monotonicity for singleton winners, and for which every alternative is viable. Then the set of all voters is a dictating set.*

*Proof.* Suppose that $P$ is a profile in which every voter has $a$ over $b$ on his ballot, but $V(P) = \{b\}$. Choose a profile $P'$ such that $V(P') = \{a\}$. Now, using down-monotonicity for singleton winners, we can first move $b$ to the bottom of every ballot in $P'$ and then repeat this for each of the other losing alternatives (in some fixed order—picture it as being alphabetical: $c, d, e, \dots$). Similarly, we can move all alternatives other than $a$ and $b$ to the bottom (in this same fixed order) of all the ballots in $P$. But then we have identical profiles with two different election outcomes. $\blacksquare$

We can reach the conclusion of Lemma 2.7 with "$V(P) = \{x\}$" replaced by the weaker assumption "$x \in V(P)$" if we replace down-monotonicity with the direct assumption that the system cannot be manipulated by an optimist or a pessimist. That is, if every voter has $a$ over $b$ and $V(P) = \{b\}$, then we can use down-monotonicity to make $\{a, b\}$ a top set. Now choose $P'$ such that $a \in V(P')$. Convert $P$ to $P'$, one ballot at a time, until $a$ becomes a winner. At this point, the voter who just changed his ballot has improved his max to his most preferred alternative $a$.

For the next four lemmas, we assume that $V$ is a voting system that cannot be manipulated by an optimist or a pessimist, and for which every alternative $x$ is viable.

**Lemma 2.8.** *Suppose that $X$ is a set of voters, $a$ and $b$ are alternatives, and $a X b$. Now assume that $c \neq a$ and $c \neq b$, and suppose that $X$ is partitioned into disjoint sets $Y$ and $Z$ (one of which may be empty). Then either $a Y c$ or $c Z b$.*

*Proof.* Consider the election in which the profile $P$ is as follows:
- Everyone in $Y$ has ballot $\langle a, b, c, \dots \rangle$.
- Everyone in $Z$ has ballot $\langle c, a, b, \dots \rangle$.
- Everyone else has ballot $\langle b, c, a, \dots \rangle$.

Because $\{a, b, c\}$ is a top set, our previous discussion guarantees that $V(P) \subseteq \{a, b, c\}$. Because $a X b, V(P) \neq \{b\}$, and so either $a \in V(P)$ or $c \in V(P)$.

Case 1: $a \in V(P)$.
For each voter in $Y$, we one-by-one move $b$ just below $c$. As we do this—changing a ballot from $B_i$ to $C_i$—$a$ remains a winner (or else we could regard $C_i$ as the true preferences and then have voter $i$ improve his max from something other than his top choice to his top choice $a$). Now, for every voter not in $Y$ or $Z$ ("Everyone else"), we one-by-one move $b$ just below $a$. Again, as we do this—changing a ballot from $B_i$ to $C_i$—$a$ remains a winner (or else we could regard $B_i$ as the true preferences and then have voter $i$ improve his min from $a$ to $b$ or $c$). But now we have produced a profile $P'$ in which $\{a, c\}$ is a top set, everyone in $Y$ prefers $a$ to $c$, everyone else prefers $c$ to $a$, and in which $a \in V(P')$. Thus, Lemma 2.6 ensures that $a Y c$, as desired.

Case 2: $c \in V(P)$.
For each voter in $Z$, we one-by-one move $a$ just below $b$. As we do this—changing a ballot from $B_i$ to $C_i$—$c$ remains a winner (or else we could regard $C_i$ as the true preferences and then have voter $i$ improve his max from something other than his top choice to his top choice $c$). Now, for every voter in $Y$, we one-by-one move $a$ just below $c$. Again, as we do this—changing a ballot from $B_i$ to $C_i$—$c$ remains a winner (or else we could regard $B_i$ as the true preferences and then have voter $i$ improve his min from $c$ to $a$ or $b$). But now we have produced a profile $P'$ in which $\{b, c\}$ is a top set, everyone in $Z$ prefers $c$ to $b$, everyone else prefers $b$ to $c$, and in which $c \in V(P')$. Thus, Lemma 2.6 ensures that $c Z b$, as desired. $\blacksquare$

**Lemma 2.9.** *Suppose $X$ is a set of alternatives and that $a X b$ for some $a$ and $b$. Then*
*(i) for all $c \neq a$, we have $a X c$, and*
*(ii) for all $c \neq b$, we have $c X b$.*

*Proof.* We never have $x \emptyset y$ for any $x$ and $y$, or else, for every profile $P$, we would have $V(P) \neq \{y\}$. Hence, (i) follows from Lemma 2.8 with $Z = \emptyset$, and (ii) follows from Lemma 2.8 with $Y = \emptyset$. $\blacksquare$

**Lemma 2.10.** *Suppose $X$ is a set of alternatives and that $a X b$ for some $a$ and $b$. Then $X$ is a dictating set.*

*Proof.* Assume that $x$ and $y$ are distinct alternatives. Using Lemma 2.9, we have:
- If $y \neq a$, then $a X b$ implies $a X y$ implies $x X y$.
- If $x \neq b$, then $a X b$ implies $x X b$ implies $x X y$.
- If $y = a$ and $x = b$, then choose some $z \neq a, b$. Then $a X b$ implies $y X x$ implies $y X z$ implies $x X z$ implies $x X y$. $\blacksquare$

**Lemma 2.11.** *Suppose that $X$ is a dictating set and that $X$ is partitioned into disjoint sets $Y$ and $Z$. Then either $Y$ is a dictating set or $Z$ is a dictating set.*

*Proof.* This is immediate from Lemmas 2.8 and 2.10. $\blacksquare$

**Lemma 2.12.** *For the kind of voting system that we are considering, there is a voter whose top choice is the unique winner whenever the winner is a singleton.*

*Proof.* It follows from Lemmas 2.7 and 2.11 that there is a voter $i$ such that $\{i\}$ is a dictating set. But this means that the only singleton winner can be the alternative at the top of voter $i$'s ballot. $\blacksquare$

We need one additional observation. Assume, then, that $V$ is a voting system that cannot be manipulated by an optimist or a pessimist, and for which every alternative $x$ is viable. Suppose voter $i$'s top choice is the unique winner whenever the winner is a singleton (as guaranteed by Lemma 2.12). Then, we claim that voter $i$'s top choice is always among the set of winners.

The argument here runs as follows. Suppose not, and choose a profile $P$ such that the alternative $x$ that is at the top of voter $i$'s ballot is not in $V(P)$, and such that $|V(P)|$ is as small as possible. We can't have $|V(P)| = 1$ by our assumption that voter $i$'s top choice is the unique winner whenever the winner is a singleton.

Assume that $V(P) = \{s_1, \dots, s_t\}$ with $t \geq 2$ and $x \notin V(P)$, and assume that voter $i$ ranks $s_1$ over $s_2$ over $\dots$ over $s_t$. Let $P'$ be any profile in which voter $i$'s ballot is the same as in $P$, but in which all the other voters have $s_1, \dots, s_t$ as a top set in that order. Now change $P$ to $P'$ one ballot at a time.

We first claim that as we change a ballot from $B_j$ to $C_j$, no new alternative $w$ gets added to the set $V(P)$ of winners, since we could then regard $C_j$ as the true preferences of that voter, and the disingenuous submission of $B_j$ would then improve the min from $w$ or worse to $s_t$. This argument covers $x = w$ as well.

Moreover, no $s_i$ can be lost from $V(P)$ by the minimality of $|V(P)|$—this is why we needed to observe that $x$ is not added to $V(P)$. But now, starting with $P'$, voter $i$ can bring $s_1$ to the top of his ballot and make the set of winners a singleton $\{s_1\}$ (because $\{s_1\}$ is then a top set), thus improving his minimum because $t \geq 2$. This completes the proof of Theorem 2.2.