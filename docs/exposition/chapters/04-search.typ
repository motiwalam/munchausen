#import "../template.typ": *

= Searching: algorithms and their limits <ch-search>

Every base has finitely many solutions (@thm-length), so a computer can in principle list them all. In practice the cost grows like $1.9^b$, and the search reaches base 43 in a few hours. This chapter describes the exact search, measures its cost, shows how much a search that may miss a few solutions can save, and proves that no search of this kind can do much better. It then explains why a proof that the problem is hard is out of reach, and why short solutions, in contrast, are cheap to find in every base at once.

== The prefix-pruned tree <sec-search-tree>

=== Search over multisets

$F(n)$ depends only on how often each digit appears, not on their order. So the search does not visit numbers. For each length $k$ from 2 to $b$ it visits the digit counts $(c_0, dots, c_(b-1))$ with $sum c_x = k$, computes the weight $S = sum c_x w(x)$, and checks two things: $S$ has exactly $k$ digits, and the digit counts of $S$ are the count vector. If both hold, $S$ is a solution, and every solution arises this way.

There are $binom(b + k - 1, k)$ count vectors with $k$ digits, and over all $k$ about $binom(2b, b) approx 4^b slash sqrt(pi b)$. The first search of the project, in Python, checked about $3.9^b$ of them #lib("6.1"). The search below builds the count vectors one digit value at a time and abandons a partial vector as soon as no completion can work. It visits about $1.9^b$ of them. @app-software describes the programs.

=== The state of a node

The tree fixes $c_(b-1)$ first, then $c_(b-2)$, and so on down. A node at digit value $v$ has fixed the counts of all digits from $v$ to $b - 1$. It stores the sum $t$ of the weights fixed so far, the number $r$ of positions still free, and the digits already known to stand at the front of $S$, the known prefix. The root for length $k$ has $t = 0$, $r = k$ and an empty prefix, and starts at the largest digit $v$ with $v^v < b^k$ (@thm-digit-bound).

The free positions hold digits below $v$. So the final sum lies in an interval:
$ "lo" = t <= S <= "hi" = t + z + r dot (v - 1)^(v - 1), $
where $z$ is the number of zeros in the known prefix, explained below. The search clips the interval to $[b^(k-1), b^k - 1]$, the $k$-digit numbers. If nothing is left, the node fails.

=== The leading-digit test

All numbers in $["lo", "hi"]$ start with the same digits, up to the first position where lo and hi differ. $S$ lies in the interval, so it starts with those digits too, and a solution must contain them. Each new leading digit $x$ must pass one test.

- If $x >= v$, its count is already fixed. If the prefix holds more copies of $x$ than $c_x$, the node fails.
- If $x < v$, its count is still open, and the digit uses up one free position. If no free position is left, the node fails.

A leading digit $x < v$ must be in the multiset even though $c_x$ is not fixed yet. The search counts it as placed: it adds $w(x)$ to $t$ at once. This narrows the interval, because lo grows by $w(x)$ and the bound for hi loses a free position worth $(v - 1)^(v - 1)$. A narrower interval can expose more leading digits, which can force more digits, and the search repeats the test until nothing new appears. A last test looks at the first unknown digit: it lies between the digits of lo and hi at that position, and if every value in that range is at least $v$ and already used up, the node fails. Knuth's program for perfect digital invariants uses the same test #cite(<knuth-backpdi>); it removes about 7% of the nodes.

At a node for digit $v$, the children try $c_v = p + e$ for $e = 0, 1, dots, r$, where $p$ is the number of copies of $v$ already in the prefix. At $v = 1$ the free positions hold ones and zeros, and the leaf tries every number of extra ones and checks the exact sum against the count vector.

#example(id: "search-ex-3435", title: [3435 in base 10])[
  The search for $k = 4$ starts at $v = 5$, because $5^5 = 3125 < 10^4 <= 6^6$.
  + One copy of 5: $t = 3125$, $r = 3$, $"hi" = 3125 + 3 dot 4^4 = 3893$. The interval $[3125, 3893]$ has the leading digit 3, which is below 5, so it is forced: $t = 3152$, $r = 2$, $"hi" = 3152 + 2 dot 256 = 3664$.
  + One copy of 4: $t = 3408$, $r = 1$, $"hi" = 3408 + 3^3 = 3435$. The interval $[3408, 3435]$ has the leading digits 34, within the one copy of 4.
  + One more 3 beyond the forced one: $t = 3435 = "lo" = "hi"$. The new digits 3 and 5 fit the counts.
  + Digits 2 and 1 get no copies. The leaf finds $S = 3435$ with the digits ${3, 3, 4, 5}$: a solution under both conventions.
  Two siblings in step 1 fail at once. With no 5, the interval $[0, 1024]$ clips to $[1000, 1024]$, which forces the digits 1 and 0, and then $"hi" = 514 < 1000$. With two 5s, $[6250, 6762]$ starts with 6, and the count of 6 is 0.
]

=== Both conventions in one pass

The conventions differ only in what a zero adds to the sum. The interval above is wide enough for both: $"lo" = t$ is the smallest sum under $0^0 = 0$, and hi adds 1 for each known zero, which covers $0^0 = 1$. The extra width is at most $k$, tiny next to $(v - 1)^(v - 1)$ except at the bottom of the tree. So one tree serves both conventions, and the leaves check each convention exactly. A combined run of base 28 visits 19,362,129 nodes, a run for one convention 19,361,945 (`docs/algorithm.md`).

#proposition(id: "search-prop-exact", title: "The search misses nothing")[
  The prefix-pruned search finds every solution of every length in base $b$, under both conventions.
]
#proof[
  Each rule removes only count vectors that cannot be solutions. The interval contains every sum that a completion of the node can reach. Every leading digit of the interval is a digit of every reachable sum, so a solution contains it. Forcing a digit removes only completions that leave it out. The first unknown digit of every reachable sum lies in the range the last test checks. A count vector reaches a leaf only if it passed every check, and the leaf compares the exact sum with the vector.
]

The implementation in Rust stores each number as one byte per base-$b$ digit in 256-bit vector registers, so addition in base $b$ needs no conversion and no bignum library. Carries resolve with a carry-lookahead identity on 64-bit masks, and one addition costs about 15 instructions. Two registers cover 62 digits and bases up to 127. The tree splits into about $10^5$ work units in a fixed order, which threads share by work stealing and a journal records, so long runs survive interruptions. Before a solution is printed, the program recomputes its sum with arbitrary-precision integers. The same engine accepts other weight tables, which @sec-model-tests and @sec-worlds-weights use. @app-software has the details.

== The cost of the exact search <sec-search-cost>

#computation(id: "search-comp-growth", title: "Growth of the exact search", src: ("6.1", "9.1"))[
  The prefix-pruned tree grows by a factor of about 1.87 to 1.90 per base: 1.87 from base 16 to 23 and 1.90 from base 30 to 43. Base 37 takes 205 seconds on the test laptop and base 40 about 25 to 36 minutes. An exact search of base 44 would take about 7 hours on 8 threads.
]

Where does the tree come from? At the top the search fixes the counts of the largest digits. The leading digits of the interval are then mostly small digits, and a small digit only adds a lower bound on its own count. So the top levels prune almost nothing. In base 21 and $k = 20$, a node at the widest level has 15 children on average #lib("6.2").

Many of these children are atypical. They give the large digits far more copies than a random number has, and such a node survives until its free positions run out. In base 21 the nodes at the widest level carry 12.5 large digits on average, against 7.6 for a random number. A measurement that drops every node with more than $s$ large digits above the random expectation (not a valid search, only a measurement of the tree) shows that the typical part grows like $1.60^b$ while the full tree grows like $1.87^b$; at base 23 the atypical nodes are 83% of the tree.

=== A formula for the tree

At the level where the counts of the $m$ largest digit values are fixed, let $L$ be the number of unknown digits of $n$ below the known prefix. Exactly $binom(L + m, m)$ count vectors for the large digits fit any given prefix. Summing these over the levels predicts the node count within a constant factor: 3.5 to 3.9 times the measured count, for bases 30 to 43 #lib("9.1"). The widest level sits near $v = 0.55 b$.

#heuristic(id: "search-heur-rates", title: "Three growth rates", src: "10.1")[
  Let the level $v$ grow with $b$ at $v = kappa b$. In the large-base limit:
  - the exact tree has about $binom(b, kappa b)$ nodes at that level, largest at $kappa = 1 slash 2$, so it grows like $2^b$;
  - the likely part, the nodes that lie above a model solution with nonnegligible probability, has entropy $H = (1 - kappa) b dot H("Poisson"(kappa))$, largest at $kappa approx 0.37$, where it equals $0.4933 b$; so it grows like $e^(0.4933) = 1.638$ per base.
  At finite bases the two rates are 1.88 and 1.55 at base 40, 1.92 and 1.56 at base 100, and 1.96 and 1.59 at base 10,000.
]

The exact search therefore gets slightly worse in larger bases. The gap between the two rates, $(2 slash 1.638)^b = 1.22^b$ in the limit, is all that skipping unlikely nodes can gain. @sec-search-entropy proves that in the model no tree search can beat $1.638^b$.

== Inexact search with a measured miss rate <sec-search-inexact>

An exact search cannot drop the atypical nodes: every node is consistent with all the information the search has, so a solution below it is not impossible, only unlikely. A search that is allowed to miss a few solutions can drop them. The engine accepts rules that do so #lib("9.2").

#tablefig(caption: [Rules of the inexact search #lib("9.2", "10.3").], id: "tab-search-rules")[
  #btable(columns: 2, align: (left, left),
    [option], [the node is dropped if],
    [`--cap c`], [one digit value has more than $c$ copies],
    [`--band z`], [the number of digits $>= v$ is more than $z$ standard deviations from its mean in a random $k$-digit number],
    [`--deficit z`], [the known prefix holds too few digits $>= v$, by more than $z$ standard deviations (a hypergeometric law)],
    [`--ratio r`], [the expected number of solutions below the node is less than $r$ times that of its parent],
    [`--zscore c`], [the log of that expected number is more than $c$ standard deviations below its mean (@sec-search-entropy)],
  )
]

The expected number of solutions below a node, used by the last two rules, is a multinomial probability:
$ E = (p!) dot v^f / (product_x "need"_x ! dot f! dot b^p), $
where $p$ is the number of unknown positions, $f$ the number of free digits below $v$, and $"need"_x$ the copies of a large digit $x$ that still have to appear. A fixed threshold on $E$ fails, because $E$ is tiny at every node of a large base. Comparing a child with its parent works. The search adds $E$ of every dropped node to a total, so each run reports its own expected number of missed solutions.

#computation(id: "search-comp-inexact", title: "Speed against misses", src: "9.3")[
  Growth fitted over bases 24 to 32; misses counted against the 93 nontrivial solutions of bases 10 to 32:
  #align(center, btable(columns: 4, align: (left, right, right, right),
    [rules], [growth per base], [nodes at base 32], [missed],
    [none (exact)], [1.891], [$2.31 dot 10^8$], [0],
    [`--ratio 1e-3`], [1.828], [$1.16 dot 10^8$], [0],
    [`--deficit 2`], [1.764], [$8.0 dot 10^7$], [1],
    [`--deficit 2 --band 2.5`], [1.712], [$4.4 dot 10^7$], [3],
    [`--ratio 1e-2 --deficit 2`], [1.693], [$2.8 dot 10^7$], [3],
    [`--deficit 1 --band 2`], [1.616], [$7.3 dot 10^6$], [19],
  ))
]

At a few percent of missed solutions the growth drops from 1.89 to about 1.71 per base. That saves a factor 5.3 at base 32, and extrapolated about 85 at base 60 and 1,700 at base 90.

How often does a rule miss in a base that no one has searched? The path from the root to a solution is fixed by the solution itself, so one can replay it and apply the rules on the way, with no search. On all 93 solutions of bases 10 to 32 the replay drops exactly the solutions that the search misses. The replay also works on _planted_ solutions: random strings whose weight has the right length, drawn with the length law of @heur-length-law. For a deficit rule with a fixed threshold the planted miss rate grows with $b$: for `--deficit 2` it is 2.5% at base 30, 9.2% at base 60 and 11.5% at base 100 #lib("9.4").

The worst standardized deficit on a path, $z_min$, behaves like the minimum of $N$ nearly independent Gaussians, which moves like $-sqrt(2 ln N)$. Its median fits $2.40 - 1.63 sqrt(ln b)$ within 0.15 for bases 20 to 300. So a threshold $c(b) = O(sqrt(ln b))$ keeps the miss rate below any fixed level, and such a threshold keeps the count vectors within $O(sqrt(b ln b))$ of their mean, which does not change the exponential rate of the typical tree #lib("9.5").

#conjecture(id: "search-conj-inexact", title: "Fixed miss rate", src: "9.5")[
  For every $delta > 0$ there is a search that, under the model, misses each solution with probability at most $delta$ and whose cost grows like $(g + o(1))^b$, where $g$ is the growth rate of the typical tree. The measurements put $g$ between 1.6 and 1.7.
]

@sec-search-entropy shows that $g = 1.638$ is the right value and gives a rule that comes close.

#example(id: "search-ex-base44", title: "Base 44")[
  Base 44 had never been searched. With `--deficit 2 --band 2.5`, both conventions, the search took 31 minutes on 8 threads and visited $2.7 dot 10^10$ nodes, against about $5.5 dot 10^11$ nodes and 7 hours for the exact search. It found one solution under $0^0 = 1$, with 43 digits and two zeros, and none under $0^0 = 0$. The model gave $0^0 = 0$ an expected 1.08 solutions, and the rules miss about 15% at this size, so base 44 has no solution under $0^0 = 0$ with probability about 0.85. Only an exact search can settle it #lib("9.3").
]

== An entropy bound for tree searches <sec-search-entropy>

The likely part of the tree grows like $1.638^b$. Is that a limit for every search, or only for the rules tried so far? It is a limit for every search that walks the tree from the top, and the proof is a short probabilistic argument. Entropy and its fluctuation, the varentropy, are reviewed in @app-prob.

#theorem(id: "thm-entropy-bound", title: "Entropy bound", src: "10.2")[
  Fix a level of the tree. In the model, let $P$ be the law of the node at that level that lies above the solution, given that a solution exists, and let $H$ and $V$ be the entropy and the varentropy of $P$. A search that tries a set $S$ of nodes at that level and contains the right node with probability $p$ satisfies
  $ |S| >= (p - V slash t^2) e^(H - t) quad "for every" t > 0. $
  Since $V$ grows linearly in $b$, taking $t = sqrt(2 V slash p)$ gives $|S| >= (p slash 2) e^(H - O(sqrt(b)))$. At the peak level $e^H$ grows like $1.638^b$, so every such search that finds a solution with probability $1 slash 2$ visits about $1.638^b$ nodes in large bases.
]
#proof[
  Let $X$ be the random node with law $P$. Call a node $x$ heavy if $P(x) >= e^(-H + t)$. A heavy node has $-ln P(x) <= H - t$, and by Chebyshev's inequality $P(-ln P(X) <= H - t) <= V slash t^2$, because $-ln P(X)$ has mean $H$ and variance $V$. So the heavy nodes together carry probability at most $V slash t^2$. Every other node in $S$ has probability below $e^(-H + t)$, so together they carry at most $|S| e^(-H + t)$. Hence $p <= V slash t^2 + |S| e^(-H + t)$, which is the claim.
]

#computation(id: "search-comp-entropy", title: "The bound at finite bases", src: "10.2")[
  At the peak level: base 40, level 17, $H = 17.3$, $sqrt(V) = 3.7$, $e^H = 3.2 dot 10^7$; base 100, level 42, $H = 43.9$, $e^H = 1.1 dot 10^19$; base 1000, level 406, $H = 453.1$, $e^H = 6.3 dot 10^196$. At base 40 the bound is 1,300 times smaller than the exact tree.
]

The theorem is a statement about the model, in which the copies of the large digits in the unknown suffix are random. For the real weights this is the assumption that @ch-model tests.

=== A rule that reaches the bound

The proof says which nodes to keep: those whose probability is close to $e^(-H)$. In the model, the expected count $E$ of @sec-search-inexact is the probability of the observed multinomial outcome, so $ln E$ has mean $-H$ and standard deviation $sqrt(V)$. The rule `--zscore c` drops a node if $ln E < -H - c sqrt(V)$, with $H$ and $V$ precomputed per level from the Poisson approximation. Near the top of the tree $ln E$ has a long left tail, so the rule applies only at the lower three quarters of the levels.

#computation(id: "search-comp-zscore", title: "The `--zscore` rule", src: "10.3")[
  #align(center, btable(columns: 4, align: (left, right, right, right),
    [rule], [growth, bases 30 to 38], [nodes at base 38], [missed],
    [exact], [1.89], [about $10^10$], [0],
    [`--zscore 3`], [1.75], [$1.17 dot 10^9$], [0 of 112, bases 10 to 38],
    [`--zscore 2`], [1.70], [$4.5 dot 10^8$], [6 of 112],
  ))
  For planted solutions the miss rate of `--zscore 3` stays between 1% and 3% from base 30 to base 300. On the 54 real solutions with at least $b - 6$ digits in bases 20 to 43 it misses 2.
]

The gain of this rule is speed at a fixed miss rate. At the thresholds that miss a few percent at base 30, the miss rate of the deficit rule grows with $b$: for `--deficit 2` it is 2.5% at base 30 and 11.5% at base 100, and $P(z_min < -2) = 0.317$ at base 300. A deficit threshold of 3 also stays near 1%, but it keeps 77% to 92% of the exact tree in bases 24 to 32, while `--zscore 3` grows like 1.75 per base #lib("9.4", "9.5"). The measured growth, 1.75, lies above the bound of 1.55 for these bases because the kept band has width $c sqrt(V)$, which grows like $sqrt(b)$ and adds a factor of about $e^(c sqrt(V) slash (2 b))$ per base, 1.15 at base 35. That factor tends to 1, so the rule's growth tends to the bound. In the limit it saves $1.22^b$ against the exact search with a fixed miss rate.

== Ideas that do not help <sec-search-fail>

@thm-entropy-bound covers searches that walk the tree from the largest digit down. A larger gain needs information that the tree does not use. The library tried the candidates below #lib("6.3", "10.4"). None changes the exponential rate.

/ Meet in the middle on digit values: Split the digits into large and small values. The small digits only change the low part of $S = A + L$, where $A$ comes from the large counts and $L$ from the small ones. But the digits of a sum are not a function of $A$ plus a function of $L$, so there is no key on which to join two lists. An exact join exists if the bottom digits of $n$ are enumerated as a string, but they must cover the weights of the small digits, about half of $n$, which needs about $b^(b slash 2)$ strings. Keying on the residue $A mod b^L$ instead costs a recomputation of the small side for each residue.
/ Meet in the middle on positions: Splitting $n$ into a top string $T$ and a bottom string $B$ gives the exact equation $T b^q - F(T) = F(B) - B$. Each side has $b^(k slash 2)$ strings. Strings cost far more than multisets: for $b = 100$ and $k = 99$ a table of at least $100^50$ entries, against $1.64^100 approx 10^(21.5)$ tree nodes #lib("22.5").
/ Lattice reduction: The equation $sum (w(s_i) - s_i b^i) = 0$ is a subset-sum problem of density about $b slash log_2 b > 1$. At that density lattice methods fail, because the relaxed problem has many solutions #cite(<lagarias-odlyzko1985>).
/ Congruences: $n$ is linear in the counts modulo $b^j$, and $n equiv "digit sum" med (mod b - 1)$. Both constraints involve every count, so they prune only near the leaves. By @thm-only-residue, $b - 1$ is the only modulus whose residue the multiset determines, and it removes a factor $b - 1$, which does not change the rate.
/ Iterating $F$: Solutions are the fixed points of $n |-> F(n)$. From random starting points the orbits run for about $1.85^b$ steps before they repeat, and in bases 14 to 22 none of 600 orbits ended at a solution. A random map on the $4^b$ multisets has orbits of length about $2^b$, and a fixed point attracts a vanishing share of starting points (@sec-model-cycles).
/ The representation technique: The best algorithms for random subset sum split a solution into two halves in many ways and filter by a residue #cite(<howgrave-graham-joux2010>) #cite(<becker-coron-joux2011>). Here the target $n$ is not fixed; it is the unknown itself. Guessing its residue costs as much as the filter saves, and the library's estimate for a full multiset search is $e^(1.28 b)$, worse than the tree.
/ Quantum backtracking: A quantum computer can search a backtracking tree of $T$ nodes in about $sqrt(T)$ steps #cite(<montanaro2018>). That gives about $1.41^b$ for the exact tree and $1.28^b$ for its likely part. It is the only known way past @thm-entropy-bound.

In short, the leading digits are the only information that a partial assignment of counts reveals cheaply, and the entropy bound says what that information is worth. A large classical speedup would need a new source of information about the low digits of $n$. The library's view, which it marks as an argument and not a proof, is that a polynomial-time exact search would have to rule out large groups of multisets without looking at them, and nothing in the data hints at a structure that allows this #lib("6.4").

== Complexity <sec-search-complexity>

Can one prove that no fast exact search exists? The answer is a precise "not with current knowledge". The background on NP, \#P and sparse sets is in @app-complexity.

=== The real problem

Let $L_m$ be the set of strings $1^b$, the base written in unary, such that base $b$ has a nontrivial solution under convention $m$. The input has size $b$, so "polynomial time" means time polynomial in $b$.

#proposition(id: "thm-np", title: "The real problem is in NP", src: "8.1")[
  $L_m$ is in NP: a solution is a certificate that can be checked in time polynomial in $b$.
]
#proof[
  A solution has at most $b$ digits, each below $b$ (@thm-length), so it takes $O(b log b)$ bits. Each weight $x^x$ has at most $b log_2 b$ bits, so computing $n$ and $F(n)$ takes polynomial time.
]

So if no algorithm decides $L_m$ in polynomial time, then P $!=$ NP. A proof that Munchausen numbers are hard to find would settle the P versus NP problem. The usual way to give evidence of hardness fails as well. $L_m$ is a tally language: it has at most one string of each length. Berman proved that if a tally language is NP-complete, then P = NP #cite(<berman1978>), and Mahaney extended this to all sparse languages #cite(<mahaney1982>). Book proved that NP contains a tally set outside P exactly when NE $!=$ E #cite(<book1974>).

#corollary(id: "search-cor-barriers", title: "Two barriers", src: ("8.1", "13.1"))[
  - A proof that $L_m$ is not in P would prove NE $!=$ E, and so P $!=$ NP.
  - A proof that $L_m$ is NP-hard would prove P = NP.
  - The counting function $b |-> N_m (b)$ is in \#P, and it is not \#P-complete under parsimonious reductions unless P = NP.
]

Neither direction is within reach. The question "is there a polynomial-time search?" is out of reach of current methods, and @sec-search-fail gives the heuristic reasons to expect that the answer is no.

=== Arbitrary weights

The barrier comes from the fixed weights, which leave one instance per base. Let the weights vary and the problem becomes hard in the usual sense.

#definition(id: "search-def-gen", title: "The problem GEN", src: "13.1")[
  Input: a base $b >= 2$ in unary and nonnegative integers $w(0), dots, w(b-1)$ in binary. Question: is there an integer $n >= b$ with $F_w (n) = n$, where $F_w (n)$ is the sum of $w(x)$ over the base-$b$ digits $x$ of $n$?
]

GEN is in NP: if $W$ is the largest weight, a solution with $D$ digits has $b^(D-1) <= D W$, so it has $O(log W)$ digits and is a short certificate #lib("13.1").

#theorem(id: "thm-gen-npc", title: "Arbitrary weights", src: "13.1")[
  GEN is NP-complete, also when $w(0) = 0$, the weights increase strictly and $W < b^(b slash 2)$. Counting the solutions of GEN is \#P-complete under parsimonious reductions.
]
#sketch[
  The reduction is from SUBSET-SUM: given positive integers $a_1, dots, a_k$ and a target $T$, is there a set $S$ with $sum_(i in S) a_i = T$? Let $B = max(T, a_i)$. Choose a prime $p$ and a base $b = p + 1$, so $p | b - 1$, and an offset $L$ with $b^(L+1) > D^* p B$, where $D^* = L + 2k + 4$ bounds the length of any solution. All of these are polynomial in the input size by Bertrand's postulate. The digits get three roles.
  - Item digits $x_i = b - 1 - i$ get the weight $x_i b^(P_i) + p a_i$ with $P_i = L + 2i$: each pays for itself at position $P_i$, plus an error $p a_i$.
  - The mandatory digit $z = b - 2 - k$ gets the weight $z b^(P_z) - p T$ with $P_z = L + 2k + 2$.
  - Every other nonzero digit is prohibited and gets the weight $y + 1$.
  For a set $S$ the number $n_S = z b^(P_z) + sum_(i in S) x_i b^(P_i)$ has $F(n_S) = n_S + p (sum_(i in S) a_i - T)$, so it is a solution exactly when $S$ hits the target. The converse is the work, in five steps. A length bound keeps every solution below $D^*$ digits. The digit-sum congruence modulo $p | b - 1$ counts the prohibited digits, since each has $w(y) - y = 1$ while designated digits have $w(x) - x equiv 0 med (mod p)$; their number is below $p$ and divisible by $p$, so it is 0. A negative total error would borrow through the empty position $L + 1$ and leave the prohibited digit $b - 1$ there. Two copies of a designated digit, which all lie above $b slash 2$, carry a small nonzero digit into the next position, which is prohibited. So every count is 0 or 1, the error is 0, and the mandatory digit must be present, because without it the error would be positive. The solutions correspond one to one to the sets $S$, which makes the reduction parsimonious; \#SUBSET-SUM is \#P-complete under parsimonious reductions through the textbook chain from \#SAT #cite(<cormen2009>). A relabeling of the roles gives strictly increasing weights.
]

The library checked the reduction by brute force on 1,890 weight tables in bases 18 to 30: in every case the solutions are exactly the numbers $n_S$ #lib("13.1"). It also records two gadgets that fail, which explain the design. Prohibited digits with weight $y$ pay for themselves at position 0, and with weight 0 they are free wildcards; the weight $y + 1$ and the congruence modulo $p$ are what remove them. Errors $a_i$ that are not multiples of $p$ let a low prohibited digit absorb them.

What does this mean for the real problem? Every algorithm that treats the weights as a black box is subject to @thm-gen-npc: the prefix-pruned tree needs only increasing weights, and the splits and joins of @sec-search-fail need nothing more. On the hard instances the weights increase and stay below $b^(b slash 2)$, the size range of $x^x$. So no algorithm that is correct for all such tables runs in time polynomial in $b$, unless P = NP. A fast algorithm for $L_m$ itself is not excluded, but it would have to use the arithmetic of $x^x$. The congruences of @sec-basics-congruences and the local obstructions of @sec-short-local are of this kind, and so far they give constant factors only. The hard instances are also unlike the real ones: their solutions have at most $b slash 2$ digits, while real solutions have about $b - 1$. Whether GEN stays hard when every solution must be long is open #lib("13.1").

=== Powers as weights

Between the free weights and $x^x$ sits the problem with weights $w(x) = x^(e(x))$, the exponents given in unary. It is in NP, and in P when all exponents are bounded by a constant, because then a solution has at most $K + 1$ digits #lib("13.1"). Whether it is NP-hard is open #q(40). The reduction above cannot be copied, and linear forms in logarithms (@app-baker) show why.

#proposition(id: "search-prop-laurent", title: "Powers cannot imitate the gadgets", src: "18.6")[
  Let $b >= 3$, $2 <= x < b$, $e >= 2$, $P >= 1$ and $L >= 0$ with $x^e != x b^P$ and $|x^e - x b^P| < b^(L+1)$. Unless $x$ and $b$ are powers of one integer and $x^(e-1) = b^P$,
  $ P - L - 1 <= 25.2 max(ln b' + 0.38, 10)^2 max(ln x, 1), quad b' = (e - 1) / (ln b) + P / max(ln x, 1). $
  Consequently, a weight table $x^(e(x))$ with $k$ item digits at distinct positions, as the reduction needs, has $k <= 25.2 max(ln(2 e_max) + 0.38, 10)^2 ln b + log_2 b$. If $b$ is polynomial in $k$, the largest exponent must be at least $exp(c sqrt(k slash log k))$, which is not polynomial.
]
#sketch[
  An item digit needs $x^(e-1)$ close to $b^P$: $|(e - 1) ln x - P ln b| < b^(L + 1 - P)$. If $x$ and $b$ are multiplicatively independent, Laurent's lower bound for linear forms in two logarithms #cite(<laurent2008>) bounds this form from below, which bounds $P - L - 1$. If they are powers of one integer, the form is a multiple of the log of that integer, so it vanishes and the item is exact; an exact item $x^(e-1) = b^P$ forces $x = r^s$ with $s < t$, where $b = r^t$ and $r$ is not a perfect power, so a base has fewer than $t <= log_2 b$ exact items #lib("18.6"). Items at distinct positions above $L + 1$ need $P - L - 1$ at least their number minus one, and $P <= e$.
]

So the hardness of the power variants is a question about the digits of powers, the same arithmetic that @ch-short and @ch-diophantine meet. One candidate for a gadget remains: digits near $b$, where $(b - c)^e = sum_i binom(e, i) (-c)^(e-i) b^i$ has explicit digits for small $c$ and $e$. No one has found a gadget of that kind, or an argument that excludes one.

== Short solutions are cheap <sec-search-short>

For a fixed number of digits the picture changes completely. @thm-one-base says that a digit string is a solution in at most one base. So the search can be turned around: fix the digits, and solve for the base.

=== Solving for the base

For a string $s$ with $k$ digits, $P_s (b) = F(s)$ has at most one root $b$, because $P_s$ increases. The program solves it with exact integers by Newton's method from above, which cannot skip the root because $P_s$ is convex and increasing on the positive axis. By @thm-digit-bound, a $k$-digit solution in base $b$ uses only digits $x$ with $x^x < b^k$. So enumerating all strings with digits up to $M$ finds every $k$-digit solution in every base $b$ with $b^k <= (M + 1)^(M + 1)$ #lib("3.1").

#proposition(id: "search-prop-fixed-length", title: "Few solutions of a fixed length", src: ("4.1", "10.5"))[
  $N_(m,k) (b) <= 2 (X_k (b) + 1)^(k-1)$, a power of $log b$ for fixed $k$. The number of bases up to $B$ with a $k$-digit solution is at most $X (X + 1)^(k-1)$ with $X = X_k (B)$.
]
#proof[
  Every digit is at most $X_k (b)$. Fix the last $k - 1$ digits, in at most $(X_k (b) + 1)^(k-1)$ ways. The leading digit $a$ must satisfy $a^a - a b^(k-1) = R$ with $R$ fixed by the other digits, and the left side is strictly convex in $a$, so at most two values work. For the second bound, every string with digits up to $X$ is a solution in at most one base.
]

So the cost per base is a power of $log b$, and a single enumeration covers all bases up to an enormous bound. @sec-short-almost-all turns the counting argument into a theorem about almost all bases.

=== The sieve

The enumeration is fast, but most of its time goes into exact root computations with numbers of hundreds of digits. A cheap test removes almost all strings first. If $Q_s = P_s - F(s)$ has no root modulo some integer $q$, then $s$ is a solution in no base (@thm-local). The test splits over positions: for a fixed prefix of $k - 1$ digits, the values of the prefix part of $Q_s$ modulo $q$, over all residues $r$, form a bit mask, and the last digit $x$ passes when $w(x) - x$ lies in the mask. So the test costs a few bit operations per string and modulus #lib("11.5").

The first version tested the 18 primes up to 61. It passed about 3 strings in 10,000 for $k = 3$ (140 of 524,880) and 6 to 12 in 10,000 for $k = 4$ to 6. It reproduced the lists of @sec-short-lists and ran about 150 times faster than the Python enumeration. The second version uses one power of each prime: a composite modulus with two prime factors tests nothing new by the Chinese remainder theorem, and a root modulo $p^e$ reduces to a root modulo $p^f$ for $f < e$. The powers of 2 and 3 gain most: modulo 2 the last digit moves $Q_s$ by even amounts only, because $x^x equiv x$, while modulo 32 the test sees much more, and modulo 27 it sees the coverings of @thm-covering #lib("19.1").

#computation(id: "search-comp-sieve", title: "The prime-power sieve", src: "19.1")[
  The default moduli are 32, 27, 25, 49 and the primes 11 to 127. Masks are built lazily, only while some last digit is alive, and residues are added as bytes without division. Against the prime sieve, on 4 threads:
  #align(center, btable(columns: 6, align: (right,) * 6,
    [$k$], [$M$], [survivors, old], [new], [time, old], [new],
    [4], [150], [615,113], [2,089], [19.5 s], [1.80 s],
    [5], [60], [507,922], [716], [49.0 s], [3.59 s],
    [6], [30], [588,869], [961], [76.7 s], [5.83 s],
    [7], [18], [596,001], [1,318], [125.1 s], [10.3 s],
  ))
  The output is identical on all lists. The speedup of about 11 comes almost entirely from the code; the prime powers and the larger primes cut the survivors by a factor of 300 to 800.
]

#computation(id: "search-comp-ranges", title: "How far the short lists reach", src: ("3.1", "11.5", "19.1"))[
  Every solution with $k$ digits, under both conventions, is known in every base up to the bound below.
  #align(center, btable(columns: 4, align: (right, right, right, right),
    [$k$], [digits up to], [complete for bases up to], [time],
    [3], [80], [$10^(51.5)$], [below 0.1 s],
    [4], [300], [$10^(186.5)$], [24 s],
    [5], [80], [$10^(30.9)$], [20 s],
    [6], [40], [$10^(11.0)$], [39 s],
    [7], [32], [$10^(7.2)$], [565 s],
    [8], [24], [23,364], [2,059 s],
  ))
]

The lists themselves are in @sec-short-lists and @app-tables. The 7-digit and 8-digit runs found no new solution under $0^0 = 1$. Under $0^0 = 0$ they found new members of the self-paying families of @ch-constructions. For longer lengths the tree search is the better tool when the base is small: no base up to 100,000 has a 9-digit solution under $0^0 = 1$, and no base up to 10,000 has one with 18, 21, 22, 24, 26 or 28 digits #lib("3.4"). Where the two methods cross over for lengths 8 to 12 is open #q(29).

== Base 100 <sec-search-base100>

Base 100 is the natural first target beyond the reach of the exact search. The engine handles bases up to 127 for numbers with at most 62 digits.

#computation(id: "search-comp-base100", title: "Base 100 up to 50 digits", src: "6.6")[
  No number with at most 50 digits in base 100 is a nontrivial solution under either convention.
  #align(center, btable(columns: 3, align: (right, right, right),
    [digits searched], [nodes], [time],
    [up to 30], [141,449], [0.055 s],
    [up to 40], [15,778,515], [0.88 s],
    [up to 45], [531,426,476], [21 s],
    [up to 50], [3,611,595,932], [139 s],
  ))
  A run up to 55 digits finished 98% of its work units in 100 minutes without a solution and was stopped.
]

The model expects about 0.002 solutions with at most 50 digits, so the result says little. The expected solutions have 97 to 100 digits (@model-heur-base100). At 1.9 per base from base 40, base 100 needs about $10^20$ seconds. Even the likely-tree rate of 1.6 per base would leave about $10^15$ seconds.

=== Solutions with $b$ digits

The original conjecture of the library said that no base above 2 has a $b$-digit solution. Under $0^0 = 0$ it is false (bases 15 and 16). Under $0^0 = 1$ the model expects a $b$-digit solution in about 8% of large bases, a little less at finite bases because of the forced top digits (@sec-model-anomalies). The search can look for $b$-digit numbers alone with `--min-digits b`, at about a quarter of the cost of a full base.

#computation(id: "search-comp-bdigit", title: [No $b$-digit solution under $0^0 = 1$], src: "8.6")[
  No base from 3 to 45 has a $b$-digit solution under $0^0 = 1$. Bases 42, 44 and 45 were searched for $b$-digit numbers only; base 42 took 29 minutes.
]

If the model is right, a counterexample is a matter of searching far enough; a proof of the conjecture would have to show that a whole family of coincidences never happens, which meets the barrier of @sec-model-empty.
