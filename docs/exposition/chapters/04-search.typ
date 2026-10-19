#import "../template.typ": *

= Searching: algorithms and their limits <ch-search>

== The prefix-pruned tree <sec-search-tree>

To be written.

== The cost of the exact search <sec-search-cost>

To be written.

== Inexact search with a measured miss rate <sec-search-inexact>

To be written.

== An entropy bound for tree searches <sec-search-entropy>

#theorem(id: "thm-entropy-bound", title: "Entropy bound", src: "10.2")[
  In the model, every search that walks the digit tree from the largest digit down and finds a solution with probability $1 slash 2$ visits about $1.638^b$ nodes in large bases.
]

To be written.

== Ideas that do not help <sec-search-fail>

To be written.

== Complexity <sec-search-complexity>

#proposition(id: "thm-np", title: "The real problem is in NP", src: "8.1")[
  The set of bases $b$, written in unary, that have a nontrivial solution is in NP.
]
#theorem(id: "thm-gen-npc", title: "Arbitrary weights", src: "13.1")[
  With arbitrary weights in place of $x^x$, deciding whether a solution exists is NP-complete, and counting the solutions is \#P-complete.
]

To be written.

== Short solutions are cheap <sec-search-short>

To be written.

== Base 100 <sec-search-base100>

To be written.
