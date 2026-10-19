#import "../template.typ": *

= Constructions and families <ch-constructions>

== Twins <sec-cons-twins>

#proposition(id: "thm-twins", title: "Twins", src: "2.1")[
  Under $0^0 = 0$, a number $n$ whose last digit is 0 is a solution if and only if $n + 1$ is a solution.
]

To be written.

== Self-paying digits <sec-cons-selfpaying>

#proposition(id: "thm-self-paying", title: "Which bases have self-paying digits", src: "2.2")[
  Write $b = r^t$ with $r$ not a perfect power. The self-paying digits of base $b$ are $a = r^s$ with $1 <= s < t$ and $t | s(r^s - 1)$, at position $k = s(r^s - 1) slash t$.
]
#proposition(id: "thm-structure-m0", title: "Structure under $0^0 = 0$", src: "2.2")[
  Under $0^0 = 0$, every solution splits uniquely into a core, a set of self-paying digits on zero positions of the core, and an optional final 1. Every such combination is a solution.
]

To be written.

== Swaps and chains <sec-cons-swaps>

To be written.

== Two-digit solutions <sec-cons-two-digit>

#proposition(id: "thm-two-digit", title: "Two-digit solutions", src: "2.4")[
  The string $(a, c)$ is a solution if and only if $a$ divides $w(c) - c$ and $b = (a^a + w(c) - c) slash a$ exceeds $a$ and $c$. The base is then $b$.
]
#theorem(id: "thm-two-two-digit", title: "Two 2-digit solutions", src: "15.2")[
  Under $0^0 = 1$, base 3 is the only base with two 2-digit solutions.
]

To be written.

== Every length under $0^0 = 0$ <sec-cons-every-length>

#proposition(id: "thm-every-length-m0", title: "Every length under $0^0 = 0$", src: "2.5")[
  Under $0^0 = 0$, every length $k >= 2$ has infinitely many bases with a $k$-digit solution.
]

To be written.

== Binomial families: every length under $0^0 = 1$ <sec-cons-binomial>

#theorem(id: "thm-binomial", title: "Binomial families", src: "22.3")[
  Let $j >= 2$, $c >= 1$, $e >= 1$, $t_i = c^(j-i) binom(j, i) e^i$ for $0 <= i <= j - 1$, and $x = e^j + sum_i t_i^(t_i)$. If $x^x = y^j$ for an integer $y$, $c | y - e$ and $b = (y - e) slash c$ exceeds every digit, then $(t_0, dots, t_(j-1), x)$ is a solution in base $b$ under both conventions.
]
#corollary(id: "thm-every-length-m1", title: "Every length under $0^0 = 1$", src: "22.3")[
  For every $k >= 3$ there are infinitely many $k$-digit solutions under $0^0 = 1$, and under $0^0 = 0$.
]

To be written.

== Self-paying blocks <sec-cons-blocks>

To be written.

== Many solutions in one base <sec-cons-many>

#proposition(id: "thm-many-m0", title: "Unbounded counts under $0^0 = 0$", src: ("4.1", "9.8"))[
  For every $n >= 3$, base $n^(n-1)$ has at least $2^(n-1) - 2$ nontrivial solutions under $0^0 = 0$. So $N_0(b)$ is unbounded.
]

To be written.

== Integers with several bases <sec-cons-multibase>

To be written.
