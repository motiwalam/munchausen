#import "../template.typ": *

= Definitions and first facts <ch-basics>

== The problem <sec-basics-def>

To be written.

== How long a solution can be <sec-basics-length>

#proposition(id: "thm-length", title: "Length bound", src: "1.2")[
  A solution in base $b$ has at most $b$ digits.
]
#proposition(id: "thm-digit-bound", title: "Digit bound", src: "1.2")[
  A $k$-digit solution in base $b$ uses only digits $x$ with $x^x < b^k$.
]

To be written.

== One base per digit string <sec-basics-polynomial>

#proposition(id: "thm-one-base", title: "One base per string", src: "1.4")[
  A digit string with at least two digits is a solution in at most one base.
]

To be written.

== The two conventions for $0^0$ <sec-basics-conventions>

#proposition(id: "thm-conventions", title: "The two conventions", src: "1.5")[
  $F_1(n) = F_0(n) + z(n)$, where $z(n)$ is the number of zero digits of $n$.
]

To be written.

== Balance <sec-basics-balance>

To be written.

== The digit-sum identity and other congruences <sec-basics-congruences>

#proposition(id: "thm-digit-sum", title: "Digit-sum identity", src: "1.6")[
  Every solution satisfies $sum_x (w(x) - x) equiv 0 med (mod b - 1)$, the sum over its digits.
]
#proposition(id: "thm-only-residue", title: "The only invariant residue", src: "10.4")[
  If $n mod M$ depends only on the digit multiset of $n$ for all $n$ with at least two digits, then $M$ divides $b - 1$.
]
#theorem(id: "thm-parity-invariant", title: "Parity invariant", src: "15.1")[
  Let $b >= 3$ and $q >= 2$. Then $F(n) equiv n med (mod q)$ for every $n >= 1$ if and only if $q = 2$, $b$ is odd and $0^0 = 0$.
]

To be written.

== Leading digits and solutions with $b$ digits <sec-basics-leading>

To be written.

== The data at a glance <sec-basics-data>

To be written.

== Earlier work <sec-basics-history>

To be written.
