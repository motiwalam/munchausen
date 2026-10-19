#import "../template.typ": *

= Short solutions and the Munchausen polynomial <ch-short>

== The complete lists <sec-short-lists>

To be written.

== Local obstructions <sec-short-local>

#proposition(id: "thm-local", title: "Local obstruction", src: "11.3")[
  If the polynomial $Q_s$ of a digit string $s$ has no root modulo some integer $q >= 2$, then $s$ is not a solution in any base.
]

To be written.

== Coverings and the residues of $x^x - x$ <sec-short-coverings>

#theorem(id: "thm-covering", title: "Covering by 27", src: "15.4")[
  Let $A(r) = sum_i s_i r^(k-i)$ and $F_0 = sum_i w(s_i)$ for a prefix $(s_1, dots, s_(k-1))$. If $A(r) - F_0 equiv.not 0 med (mod 3)$ and $A(r) - F_0 equiv.not 2 med (mod 27)$ for every residue $r$ modulo 27, then no string $(s_1, dots, s_(k-1), x)$ with $x >= 1$ is a solution in any base, under either convention.
]

To be written.

== Galois groups and reducibility <sec-short-galois>

To be written.

== The root heuristic <sec-short-heuristic>

To be written.

== The square class and near-integers <sec-short-square>

#theorem(id: "thm-square-class", title: "Large leading digit", src: "8.2")[
  Fix $k >= 2$ and $k - 1$ lower digits below a bound $B$, and let the leading digit $x$ vary with $x^(x-1)$ a perfect $(k-1)$-th power. For $x$ above an explicit bound, the only solutions are the self-paying families $(x, 0, dots, 0, 0)$ and $(x, 0, dots, 0, 1)$ under $0^0 = 0$, and $(x, 1)$ under $0^0 = 1$.
]

To be written.

== Almost all bases have no short solution <sec-short-almost-all>

#theorem(id: "thm-almost-all", title: "Almost all bases", src: "20.1")[
  For every $epsilon > 0$, almost all bases $b$ have no solution with $2 <= k <= (1 - epsilon) ln b slash ln ln b$ digits, under either convention.
]

To be written.

== Other roots: negative bases and rational roots <sec-short-roots>

To be written.

== Bases with a 2-digit and a 3-digit solution <sec-short-two-three>

To be written.
