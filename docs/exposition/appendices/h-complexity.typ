#import "../template.typ": *

= Complexity: NP, \#P and sparse sets <app-complexity>

@sec-search-complexity asks whether Munchausen numbers can be found fast, and why the answer is out of reach. The tools are the classes P and NP, reductions, counting classes, and the special status of problems with very few instances. This appendix explains them. Garey and Johnson @garey-johnson1979 and Arora and Barak @arora-barak2009 are standard references; @cormen2009[chapter 34] is a short introduction.

== P, NP and certificates <sec-app-complexity-np>

A decision problem is a set $L$ of strings over a finite alphabet: the instances whose answer is "yes". The size of an instance is its length as a string. So the encoding matters. The base $b$ written in binary has about $log_2 b$ symbols; written in unary, as $1^b$, it has $b$ symbols.

#definition(id: "app-complexity-def-np", title: "P and NP")[
  $L$ is in P if a deterministic algorithm decides membership in time polynomial in the size $s$ of the instance. $L$ is in NP if there is a polynomial $p$ and a polynomial-time verifier $V$ such that an instance $u$ is in $L$ exactly when some certificate $c$ of length at most $p(s)$ makes $V(u, c)$ accept.
]

A Munchausen number is its own certificate. Let $L_m$ be the set of strings $1^b$ such that base $b$ has a nontrivial solution under $0^0 = m$. A solution has at most $b$ digits (@thm-length), so it can be written with $O(b log b)$ bits, and checking $F(n) = n$ takes time polynomial in $b$. So $L_m$ is in NP (@thm-np). Note the unary encoding: in binary the same problem would be in NEXP, a much larger class, because a solution is exponentially long in $log b$.

== Reductions and NP-completeness <sec-app-complexity-npc>

A polynomial-time reduction from $L$ to $L'$ is a polynomial-time map $f$ with $u in L$ exactly when $f(u) in L'$. A problem is NP-hard if every problem in NP reduces to it, and NP-complete if it is also in NP. The first NP-complete problem was SAT, the satisfiability of Boolean formulas (Cook and Levin). Thousands followed. The one used in the library is SUBSET-SUM.

#definition(id: "app-complexity-def-subset", title: "SUBSET-SUM")[
  Given positive integers $a_1, dots, a_k$ and a target $T$, all in binary, is there a set $S$ of indices with $sum_(i in S) a_i = T$?
]

SUBSET-SUM is NP-complete @garey-johnson1979. It is hard only because the numbers are written in binary: dynamic programming solves it in time polynomial in $k$ and $T$. The Munchausen equation looks like a subset sum, $sum_i (s_i b^i - w(s_i)) = 0$, but with the digits as unknowns and the target equal to the number itself.

The library proves that the problem with arbitrary weights is NP-complete (@thm-gen-npc). The instance is a base $b$ in unary and a table of weights $w(0), dots, w(b - 1)$ in binary, and the question is whether some $n >= b$ equals the sum of the weights of its digits. The reduction from SUBSET-SUM builds a weight table whose solutions correspond one to one to the subsets with sum $T$. Each item $a_i$ becomes a digit $x_i$ at a position $P_i$, with weight $x_i b^(P_i) + p a_i$ for a prime $p$ dividing $b - 1$; the target becomes a mandatory digit with weight $z b^(P_z) - p T$; every other digit gets the weight $y + 1$, and the digit-sum identity modulo $p$ (@thm-digit-sum) forbids it. The details are in #lib("13.1").

== Counting: \#P <sec-app-complexity-sharpp>

#definition(id: "app-complexity-def-sharpp", title: [\#P])[
  A function $f$ from strings to nonnegative integers is in \#P if there is a polynomial-time verifier $V$ and a polynomial $p$ such that $f(u)$ is the number of certificates $c$ of length at most $p(s)$ that make $V(u, c)$ accept.
]

A reduction is parsimonious if it preserves the number of solutions, not only their existence. Valiant @valiant1979 introduced \#P and showed that counting can be hard even when deciding is easy. \#SAT is \#P-complete under parsimonious reductions, and so is \#SUBSET-SUM. The reduction above is parsimonious, so counting the solutions of a general weight table is \#P-complete. The counting function $b |-> N_m (b)$ of the real problem is in \#P.

== Sparse and tally sets <sec-app-complexity-sparse>

$L_m$ has a special shape: for each length it contains at most one string, $1^b$. Such a set is a tally set. A set is sparse if it contains at most polynomially many strings of each length. Sparse sets carry very little information, and this limits what one can prove about them.

#theorem(id: "app-complexity-berman", title: "Berman, Mahaney", status: "cited")[
  If a sparse set is NP-hard under polynomial-time many-one reductions, then P = NP.
]

Berman @berman1978 proved this for tally sets, and Mahaney @mahaney1982 for all sparse sets. So, unless P = NP, $L_m$ is not NP-complete, and no reduction can give evidence that Munchausen numbers are hard to find. On the other side, $L_m$ is in NP, so a proof that $L_m$ is not in P would prove P $!=$ NP. Book's theorem sharpens this.

#theorem(id: "app-complexity-book", title: "Book", status: "cited")[
  NP contains a tally set that is not in P if and only if NE $!=$ E. Here E is the class of problems solvable in time $2^(O(s))$, and NE its nondeterministic version.
]

See @book1974. So a proof that no polynomial algorithm finds Munchausen numbers would prove NE $!=$ E, a statement stronger than P $!=$ NP. Both directions are therefore closed to current methods: a lower bound would separate complexity classes, and hardness would collapse them. This is the barrier of @sec-search-complexity. What remains possible is an algorithm that uses the arithmetic of $x^x$. Every algorithm that treats the weights as an arbitrary table is subject to the NP-completeness of the general problem.

== Lattices and low-density subset sums <sec-app-complexity-lattice>

Some subset-sum instances are easy. If the numbers $a_i$ are very large compared with their count $k$, the density $k slash log_2 max a_i$ is small, and the solution is usually the shortest vector of a lattice built from the $a_i$. Lattice reduction (the LLL algorithm) then finds it; Lagarias and Odlyzko @lagarias-odlyzko1985 analyse this. The Munchausen equation, seen as a subset sum over digit placements, has density about $b slash log_2 b$, far above 1. At that density the relaxed lattice problem has many short vectors, and the method fails (#lib("6.3")). The best generic algorithms for random subset sums (Howgrave-Graham and Joux @howgrave-graham-joux2010, Becker, Coron and Joux @becker-coron-joux2011) also do not apply, because here the target is the unknown itself (@sec-search-fail).
