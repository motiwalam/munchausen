#import "../template.typ": *

= The probabilistic model <ch-model>

== The counts per base <sec-model-data>

To be written.

== The basic model and the large-base limit <sec-model-basic>

#heuristic(id: "heur-length-law", title: "The length law", src: "5.2")[
  In the large-base limit a base has on average one solution per convention before the parity effect. Its length is $b$, $b - 1$, $b - 2$, $b - 3$ with probabilities about 8.0%, 55.2%, 23.2%, 8.6%, and shorter lengths are rarer by a factor of about $e$ per digit.
]

To be written.

== The digit-sum identity and the parity effect <sec-model-refined>

To be written.

== Testing the model by changing the weights <sec-model-tests>

To be written.

== Near-solutions and the defect spectrum <sec-model-defects>

To be written.

== A Poisson limit theorem <sec-model-poisson>

#theorem(id: "thm-poisson", title: "Poisson approximation", src: "13.2")[
  In the coupled model, the joint law of $(N_0, N_1)$ is within total variation distance $O(1 slash b)$ of a bivariate Poisson law. The refined version needs an assumption on the residues of $x^x$.
]

To be written.

== Empty bases <sec-model-empty>

To be written.

== Length against base <sec-model-window>

#conjecture(id: "conj-window", title: "Length window", src: "10.5")[
  Under $0^0 = 1$ and for every $epsilon > 0$, only finitely many solutions with $k >= 3$ digits outside algebraic families lie in a base $b > k + ln k + (1 + epsilon) ln ln k$, and infinitely many lie in a base $b > k + ln k + (1 - epsilon) ln ln k$.
]

To be written.

== Cycles of $n |-> F(n)$ <sec-model-cycles>

To be written.

== Anomalies and how they were resolved <sec-model-anomalies>

To be written.
