#import "../template.typ": *

= The probabilistic model <ch-model>

The constructions of @ch-constructions explain a few solutions, mostly short ones and mostly in special bases. The long solutions near $b$ digits show no structure at all. This chapter treats them as coincidences. A digit multiset has some small chance to reproduce itself, and the chance can be computed. The resulting model predicts how many solutions a base has, how long they are, and why odd bases have more of them. It survives every test the library has tried on it, with one exception in the factorial number system and one in function fields (@sec-worlds-factorial, @sec-worlds-ffield).

Two warnings before we start. First, everything in this chapter marked "heuristic" is a statement about a random model, not about $x^x$. The model is tested against data, and the tests are the evidence. Second, the data are small: a few dozen bases with one or two solutions each. So the chapter often asks whether a deviation is chance. The answer depends on how the question was chosen, a point that @sec-model-anomalies explains.

== The counts per base <sec-model-data>

The exhaustive search of @ch-search has found every solution in bases 2 to 41 and in base 43, under both conventions. The full table is in @sec-basics-data and @app-tables. Here are the facts that the model must explain.

- Most bases have one to three nontrivial solutions under each convention. The largest count up to base 43 is 7, in base 15 under $0^0 = 0$.
- The longest solution usually has $b - 1$ digits: in 23 of the 29 bases from 10 to 41 that have a solution #lib("4.3"). Only bases 15 and 16 have a $b$-digit solution, both under $0^0 = 0$.
- Odd bases have more solutions under $0^0 = 0$. Over bases 10 to 41, odd bases average 2.56 solutions and even bases 1.56. Under $0^0 = 1$ the averages are 1.81 and 1.69 #lib("4.3").
- The counts of the two conventions are correlated, 0.56 over bases 10 to 41. A solution without the digit 0 counts under both conventions (@thm-conventions), and 35 of the 56 solutions under $0^0 = 1$ in these bases are zero-free.
- Bases 19, 27 and 35 have no solution under either convention. They are the only empty bases from 3 to 41, and base 43 has solutions.

If each base had a Poisson number of solutions with the mean of the refined model of @sec-model-refined, bases 10 to 39 would show the distribution of @tab-model-poisson-shape. The counts follow the Poisson shape roughly. The upper tail is heavier, because twins and constructed solutions come in groups and small bases have extra solutions.

#tablefig(caption: [Bases 10 to 39 with exactly $n$ nontrivial solutions, observed against a Poisson law with the mean of the refined model #lib("4.4").], id: "tab-model-poisson-shape")[
  #btable(columns: 8, align: (left,) + (right,) * 7,
    [], [$n = 0$], [1], [2], [3], [4], [5], [6+],
    [$0^0 = 0$, expected], [6.3], [8.9], [7.1], [4.2], [2.1], [0.9], [0.4],
    [$0^0 = 0$, observed], [6], [9], [5], [3], [3], [3], [1],
    [$0^0 = 1$, expected], [8.6], [10.7], [6.7], [2.8], [0.9], [0.2], [0.1],
    [$0^0 = 1$, observed], [6], [7], [9], [4], [3], [1], [0],
  )
]

Some counts are forced by structure. Under $0^0 = 0$ solutions ending in 0 or 1 come in twins (@thm-twins), so $N_0 (b)$ has the parity of the number of solutions whose last digit is at least 2. Bases with self-paying digits always have solutions under $0^0 = 0$ (@thm-structure-m0), and the count is unbounded along special bases (@thm-many-m0). The model ignores all of this. It describes the generic coincidences, and it should be compared with the data after the families are set aside or in large bases where they are rare.

== The basic model and the large-base limit <sec-model-basic>

Fix a length $k$ and a digit multiset $c$ with $k$ digits. Its weight $S(c) = sum_x c_x w(x)$ is one fixed number. The multiset gives a solution exactly when the base-$b$ digits of $S(c)$ form the multiset $c$. The model replaces the digits of $S(c)$ by random digits.

#definition(id: "model-def-basic", title: "Basic model", src: "5.1")[
  For each multiset $c$ of $k$ digits, the digits of $S(c)$ are drawn uniformly among the $k$-digit strings with a nonzero leading digit, independently for different multisets. The multiset is a _model solution_ if the drawn string has the multiset $c$.
]

The chance that a random $k$-digit string has a given multiset $c$ is the same for the drawn string as for a random string $n$. Summing over all multisets $c$ whose weight has $k$ digits gives a formula that is easy to estimate by sampling.

#proposition(id: "model-prop-ek", title: "Expected count per length", src: "5.1")[
  In the basic model, the expected number of $k$-digit solutions is
  $ E_k = P(F(n) "has exactly" k "digits"), $
  where $n$ is a uniform random $k$-digit number.
]
#proof[
  Let $p(c)$ be the probability that a uniform $k$-digit string has multiset $c$. A multiset $c$ whose weight has $k$ digits is a model solution with probability $p(c)$, and one whose weight has another length is never one. So the expected count is the sum of $p(c)$ over the multisets with $k$-digit weight. That is the probability that a uniform $n$ has such a multiset, and $F(n) = S(c)$.
]

The formula says something striking. Sum over all lengths. The events "$F(n)$ has $k$ digits" for a $k$-digit random $n$ are different events for different $k$, but in a large base they behave like a partition of one event. So the expected total is close to 1.

Let $b$ grow with $J = b - k$ fixed. The digit counts of a random $k$-digit string become independent Poisson variables with mean $k slash b -> 1$. A digit $b - y$ weighs
$ (b - y)^(b - y) = b^(b-y) (1 - y slash b)^(b-y) approx e^(-y) b^(b - y), $
so the largest digit present decides the length of $F(n)$. One copy of $b - 1$ weighs about $b^(b-1) slash e$, so $c$ copies give $F approx (c slash e) b^(b-1)$. This crosses $b^(b-1)$, the smallest $b$-digit number, when $c >= 3$.

#heuristic(id: "heur-length-law", title: "The length law", src: ("5.2", "10.5"))[
  In the large-base limit a base has on average one solution per convention before the parity effect of @sec-model-refined. Its length is $b$, $b - 1$, $b - 2$, $b - 3$, $b - 4$ with probabilities about 8.0%, 55.2%, 23.2%, 8.6%, 3.2%, and each further digit of shortfall costs a factor of about $e$. The expected number of solutions with $J = b - k >= j$ is about $e^(-(j-1))$ for $j >= 1$.
]
#sketch[
  The cases are disjoint and cover almost everything. Write $c_x$ for the Poisson(1) counts.
  - $k = b$: the sum needs at least $b$ digits, so at least 3 copies of $b - 1$. The probability is $P("Poisson"(1) >= 3) = 1 - (5 slash 2) e^(-1) = 0.080$.
  - $k = b - 1$: one or two copies of $b - 1$ put $F$ between $b^(b-2)$ and $b^(b-1)$, with probability $(3 slash 2) e^(-1) = 0.552$.
  - $k = b - j$ for $j >= 2$: no digit above $b - j$ and at least one copy of $b - j$. This has probability $e^(-(j-1)) (1 - e^(-1))$, which gives 0.233, 0.086, 0.032 for $j = 2, 3, 4$.
  The five numbers add up to 0.983, and the tail adds the rest to 1. In each case the event "$F(n)$ has $k$ digits" has the stated probability, and @model-prop-ek turns it into the expected count.
]

The law holds well at finite $b$. @tab-model-length-law shows the exact model at bases 50 to 800 #lib("10.5"). For $J$ up to about $ln b$ the values match the limit. Beyond that they are about three times the limit, a bump that @sec-model-window explains.

#tablefig(caption: [Expected number of solutions with $J = b - k$ in the basic model #lib("10.5").], id: "tab-model-length-law")[
  #btable(columns: 6, align: (right,) * 6,
    [$J$], [base 50], [base 100], [base 200], [base 800], [limit],
    [0], [0.078], [0.080], [0.081], [0.078], [0.080],
    [1], [0.554], [0.554], [0.546], [0.553], [0.552],
    [2], [0.237], [0.234], [0.233], [0.231], [0.233],
    [4], [0.036], [0.034], [0.033], [0.031], [0.032],
    [8], [0.0029], [0.0021], [0.0018], [0.0010], [0.0006],
    [12], [0.00030], [0.00009], [0.00002], [0.00003], [0.00001],
  )
]

#remark(id: "model-rem-universal-one")[
  The total of 1 does not depend on the details of $x^x$. It only needs the length of $F(n)$ to be nearly independent of the length of $n$ near the critical length, so that $sum_k P(ell(F_k) = k)$ is close to $sum_ell P(ell(F) = ell) = 1$. This is why "about one solution per base" holds in every number system of @ch-worlds where digits can move freely. The length shares, in contrast, depend on how high the top weight sits between two powers of the base, and they change from system to system (@sec-worlds-universal).
]

== The digit-sum identity and the parity effect <sec-model-refined>

The basic model forgets one fact. Every integer satisfies $n equiv (text("digit sum of") n) med (mod b - 1)$, because $b equiv 1$. For a solution this becomes the identity of @thm-digit-sum: the multiset must satisfy $sum_x c_x (w(x) - x) equiv 0 med (mod b - 1)$.

#definition(id: "model-def-refined", title: "Refined model", src: "5.3")[
  The digits of $S(c)$ are drawn uniformly among the $k$-digit strings whose digit sum is congruent to $S(c)$ modulo $b - 1$.
]

A multiset that meets the identity becomes $b - 1$ times as likely to be a solution, and a multiset that fails it becomes impossible. On average nothing changes, unless the identity holds more often than one time in $b - 1$. It does, because of the prime 2.

#heuristic(id: "model-heur-parity", title: "Parity factors", src: ("5.3", "17.3"))[
  In the large-base limit the refined model multiplies the expected count of the basic model by these factors:
  #align(center, btable(columns: 3, align: (left, right, right),
    [], [even base], [odd base],
    [$0^0 = 0$], [1], [2],
    [$0^0 = 1$], [1], [$1 + e^(-2) approx 1.135$],
  ))
  More generally, with $w(0) = m$, the odd-base factor is 2 for even $m$ and $1 + e^(-2)$ for odd $m$.
]
#sketch[
  For every $x >= 1$, $x^x equiv x med (mod 2)$. In an odd base $b - 1$ is even. Under $0^0 = 0$ every term $w(x) - x$ is then even, so the identity holds modulo the 2-part of $b - 1$ for every multiset. Modulo the odd part it holds with the usual chance. So the share of multisets that meet the identity is twice the random share, and the count doubles. Under $0^0 = 1$ a zero contributes $1 - 0 = 1$, so the identity modulo 2 says that the number of zeros is even. The zero count is close to Poisson(1), and $P("Poisson"(1) "even") = (1 + e^(-2)) slash 2$. Twice that is the factor. For an odd prime $p$ dividing $b - 1$, the residues of $x^x - x$ modulo $p$ are spread, and a sum of about $b$ of them is close to uniform, so the factor is 1. In an even base $b - 1$ is odd and nothing changes.
]

So a large odd base expects two solutions under $0^0 = 0$ and about 1.135 under $0^0 = 1$, and a large even base expects one under each. Averaged over all bases, the model predicts 1.5 solutions per base under $0^0 = 0$ and about 1.07 under $0^0 = 1$ #lib("7.4").

The factor 1 for odd primes is the one assumption of this section that is not obvious. It says that the residues of $x^x$ modulo the odd prime powers in $b - 1$ spread evenly over the multisets whose weight has the right length. @sec-model-poisson calls it Assumption R. It is open (@sec-open-list).

=== The model against the data

#computation(id: "model-comp-totals", title: "Totals in bases 10 to 38", src: "5.4")[
  Nontrivial solutions in bases 10 to 38, summed over all lengths:
  #align(center, btable(columns: 5, align: (left, left, right, right, right),
    [convention], [bases], [basic model], [refined model], [observed],
    [$0^0 = 0$], [even], [17.2], [17.3], [22],
    [$0^0 = 0$], [odd], [16.0], [32.5], [38],
    [$0^0 = 1$], [even], [17.2], [17.4], [26],
    [$0^0 = 1$], [odd], [16.0], [19.1], [26],
  ))
]

The refined model explains the large difference between odd and even bases under $0^0 = 0$: the basic model predicts the same for both, the data show nearly twice as many in odd bases (38 against 22), and the refined model predicts a factor of 1.88. The remaining surplus sits in small bases, which contain the algebraic families of @ch-constructions. For bases 20 to 38 under $0^0 = 1$ the basic model expects 20.6 and 26 occur, 1.2 standard deviations.

The model was built before bases 39 to 41 were searched, so these bases are a fair test. The model expected 5.19 solutions under $0^0 = 0$ and 3.38 under $0^0 = 1$; the search found 6 and 4 #lib("5.7"). All six new solutions have $b - 1$ digits, the most likely length.

=== Predictions

#heuristic(id: "model-heur-base100", title: "Base 100", src: ("5.6", "6.6"))[
  Base 100 is even, so no parity factor applies. The model expects 1.01 nontrivial solutions per convention: 0.55 with 99 digits, 0.24 with 98, 0.09 with 97, 0.08 with 100 and 0.06 with fewer.
]

The search has excluded every base-100 solution with at most 50 digits (@sec-search-base100). The model gives such solutions a total chance of about 0.002, so this is no test. A search of base 100 itself is out of reach (@sec-search-cost).

== Testing the model by changing the weights <sec-model-tests>

A model built to fit 40 bases could fit them by accident. The strongest tests change the weights and ask whether the model follows. The engine of @ch-search accepts other weight tables (@sec-search-tree), so the same exact search runs in worlds that the model describes differently.

=== Random weights keep the count and lose the parity effect

With `--perturb`, each weight $x^x$ with $x >= 2$ gets a random extra amount of up to a quarter of its size. With `--keep-residues` the extra amount is a multiple of $2(b - 1)$, so the residues of the weights stay the same.

#computation(id: "model-comp-perturb", title: "Perturbed weights", src: "9.6")[
  Solutions with at least $b - 6$ digits in bases 16 to 28, three random seeds per base:
  #align(center, btable(columns: 3, align: (left, right, right),
    [weights], [$0^0 = 0$], [$0^0 = 1$],
    [refined model], [20.1], [14.9],
    [true weights], [16], [16],
    [random perturbation], [13.7], [13.3],
    [perturbation that keeps residues], [19.6], [14.9],
  ))
]

Random weights lose the extra solutions of odd bases under $0^0 = 0$, and the total falls to the value of the basic model. Weights that keep their residues bring the effect back, at exactly the size of the refined model. So the residues of $x^x$ cause the parity effect, and nothing else in the arithmetic of $x^x$ matters for the counts. The perturbed worlds also reproduce the emptiness law of @sec-model-empty: in 240 runs on even bases 16 to 27, 47 were empty against 44.8 predicted, and in 240 runs on odd bases, 16 against 20.6 #lib("9.7").

=== Forced residues: a factor of seventeen

The sharpest test forces the residues. The option `--set-residue r` raises each weight $w(x)$, $x >= 1$, by less than $b - 1$, so that $w(x) equiv x + r med (mod b - 1)$. Let the digit 0 weigh $z$.

#proposition(id: "model-prop-forced", title: "Forced residues", src: "17.2")[
  Suppose $w(x) equiv x + r med (mod b - 1)$ for every digit $x >= 1$ and $w(0) = z$. A $k$-digit solution with $c_0$ zeros satisfies $r(k - c_0) + z c_0 equiv 0 med (mod b - 1)$. In particular:
  #align(center, btable(columns: 4, align: (right, right, left, left),
    [$r$], [$z$], [condition on a solution], [allowed lengths],
    [0], [0], [none], [all],
    [0], [1], [$c_0 equiv 0 med (mod b - 1)$], [all, with no zero (or $b - 1$ zeros)],
    [1], [1], [$k equiv 0 med (mod b - 1)$], [only $k = b - 1$],
    [1], [0], [$k - c_0 equiv 0 med (mod b - 1)$], [$k = b - 1$ without zeros, or $k = b$ with one zero],
  ))
]
#proof[
  This is @thm-digit-sum with $w(x) - x equiv r$ for nonzero digits and $w(0) - 0 = z$.
]

With $r = 0$ and $z = 0$ the identity holds for every multiset, so the refined model predicts $b - 1$ times as many solutions as for random residues: in bases 12 to 24, about 17 times as many. With $r = 1$ and $z = 1$ only solutions with exactly $b - 1$ digits survive, and the model predicts $(b - 1)$ times the 55.2% share of that length.

#computation(id: "model-comp-forced", title: "Forced residues in bases 12 to 24", src: "17.2")[
  Bases 12 to 24, seeds 1 to 8 (104 runs per weight set, $sum (b - 1) = 1768$), solutions with at least $b - 6$ digits, against the refined model computed with the exact weights of each run:
  #align(center, btable(columns: 6, align: (left, left, right, right, right, right),
    [weights], [convention], [observed], [model], [per $b - 1$], [limit],
    [`--perturb`], [$0^0 = 0$], [98], [111.8], [], [],
    [`--perturb`], [$0^0 = 1$], [109], [111.8], [], [],
    [`--set-residue 0`], [$0^0 = 0$], [1955], [1891.4], [1.106], [1.000],
    [`--set-residue 0`], [$0^0 = 1$], [845], [789.8], [0.478], [0.368],
    [`--set-residue 1`], [$0^0 = 1$], [1030], [984.7], [0.583], [0.552],
    [`--set-residue 1`], [$0^0 = 0$], [454], [453.1], [0.257], [0.233],
  ))
]

Forcing $w(x) equiv x$ multiplies the count by $1955 slash 103.5 = 18.9$; the model predicts 16.9, and the mean of $b - 1$ is 17.0. With $w(x) equiv x + 1$ under $0^0 = 1$, all 1030 solutions have exactly $b - 1$ digits, as the identity demands. All four forced cases lie within 7% of the model. A seventeen-fold change in the count, predicted to a few percent by a model with no fitted parameter, is the best evidence that the model captures the mechanism.

Two details differ from a Poisson law, and both are structural. The counts per run scatter twice as much as Poisson counts, because forced residues fix the small weights and create families: in base 21 with `--set-residue 1`, $w(2) - w(1) = w(3) - w(2) = b$, so a digit 1, 2 or 3 in the second-to-last place gives three solutions at once. And short solutions become four times too common under `--set-residue 0`, for an algebraic reason: writing $w(x) = x + k_x (b - 1)$, a 2-digit string $(a, c)$ is a solution exactly when $a = k_a + k_c$, and $k_1 = 0$, $k_2 = 1$ for every $b >= 4$, so $(1, 2)$ and $(2, 2)$ are solutions in every base and for every seed #lib("17.2").

=== The value of $0^0$ as a free parameter

Let the digit 0 weigh $m$ under the second convention, for $m$ from $-2$ to 3. For $m$ other than 0 and 1 there are no twins and no self-paying families, so these worlds test the model without the families. @model-heur-parity predicts an odd-base factor of 2 for even $m$ and $1 + e^(-2)$ for odd $m$; at finite bases the model gives 2.00 to 2.02 and 1.19 to 1.22.

#computation(id: "model-comp-zero-m", title: [The convention $0^0 = m$], src: "17.3")[
  Bases 10 to 30, solutions with at least one zero, pooled by the parity of $m$:
  #align(center, btable(columns: 5, align: (left, left, right, right, right),
    [$m$], [bases], [observed], [model], [$P("at least observed")$],
    [even ($-2, 0, 2$)], [even], [16], [21.7], [0.91],
    [even ($-2, 0, 2$)], [odd], [42], [39.5], [0.37],
    [odd ($-1, 1, 3$)], [even], [28], [21.7], [0.11],
    [odd ($-1, 1, 3$)], [odd], [11], [10.9], [0.53],
  ))
]

The parity factor follows the parity of $m$, as predicted. Zero-free solutions are set aside in this table because they are solutions for every $m$ at once and would be counted six times. There are 24 of them in these bases, against 16.5 expected #lib("17.3").

== Near-solutions and the defect spectrum <sec-model-defects>

A base with one solution gives one data point. The defect spectrum turns each base into hundreds of data points.

#definition(id: "model-def-defect", title: "Defect spectrum", src: "11.1")[
  For a base $b$ and an integer $D$, let $N_D (b)$ be the number of integers $n$ with at least two digits and $n - F(n) = D$. The numbers counted by $N_D (b)$ with $D != 0$ are _near-solutions_ with offset $D$.
]

The search finds $N_D (b)$ exactly by starting the interval of @sec-search-tree at $D$ in place of 0. If the model is right, $D = 0$ is not special. An offset $D$ in the residue class of 0 modulo $2(b - 1)$ keeps the digit-sum identity and the parity, so it is another draw of the same coincidence, with the true weights $x^x$ and all their arithmetic. The mean of $N_D (b)$ over such offsets estimates the expected number of solutions of base $b$ without any model. Call it $lambda_m (b)$.

Short numbers need care, because $n = F(n) + D$ needs $n > D$. So the comparison counts only numbers with at least $b - 6$ digits, where every offset below $10^6$ sees the same lengths.

#computation(id: "model-comp-spectrum", title: "Solutions against their near-solutions", src: "11.1")[
  Bases 12 to 32, offsets $D = j(b - 1)$ with even $j$ up to 120, numbers with at least $b - 6$ digits:
  #align(center, btable(columns: 3, align: (left, right, right),
    [group], [solutions ($D = 0$)], [predicted by the offsets],
    [$0^0 = 0$, even bases], [13], [10.9],
    [$0^0 = 0$, odd bases], [20], [22.2],
    [$0^0 = 1$, even bases], [15], [12.8],
    [$0^0 = 1$, odd bases], [15], [14.0],
  ))
  Within a base the counts $N_D$ at single offsets have variance-to-mean ratio 0.98 (median over 42 cases). Across bases, $sum (N_0 - lambda)^2 slash lambda = 44.6$ over 42 cases with the clustered calibration of @sec-model-evidence ($P = 0.36$; 48.8 with the naive one).
]

So solutions are ordinary draws. The count at a single offset is Poisson. Across bases the number of solutions scatters around the base's own mean as a Poisson draw would. One caution, which @sec-model-evidence makes precise: the offsets are not independent of each other, so the mean $lambda$ is less precise than 60 independent offsets would make it. Odd bases under $0^0 = 0$ have twice as many near-solutions as even ones, at every offset in the class: the parity effect, now seen without the model. A base does not "know" whether it has a solution. The empty base 19 has an ordinary spectrum, with $lambda = 1.02$ under $0^0 = 1$ and 1.35 under $0^0 = 0$, inside the range 0.88 to 2.17 of the other bases.

=== How well the model predicts a single base

The ratio $lambda slash "model"$ averages 0.98 under $0^0 = 0$ and 1.12 under $0^0 = 1$ over bases 12 to 32. So the model is right on average. Its spread from base to base was first measured at about 20%, twice the sampling error of the offsets #lib("11.2a"). With the clustered variance of @sec-model-evidence about half of that excess disappears; it was an artefact of treating the offsets as independent. Part of the rest comes from the forced top digits. The top digits of $F(c)$ are fixed by the counts of the largest digits, and those top digits must also be in the multiset. The model treats them as random. A model that reads the top $t$ digits off $F$ and draws only the rest follows the bases more closely.

#computation(id: "model-comp-top", title: "Forced top digits and the scatter", src: ("23.5", "26.4"))[
  Bases 12 to 32, lengths $b - 6$ to $b$, 400,000 sampled multisets per base and length. Chi-square of $lambda slash "model"$ on 21 bases, with the naive variance of the offset means and with the clustered one:
  #align(center, btable(columns: 5, align: (right, right, right, right, right),
    [top digits forced, $t$], [$0^0 = 0$: naive], [clustered], [$0^0 = 1$: naive], [clustered],
    [0 (refined model)], [97.0], [41.4 ($P = 0.005$)], [95.7], [43.3 ($P = 0.003$)],
    [3], [68.2], [30.2 ($P = 0.09$)], [75.7], [34.7 ($P = 0.03$)],
    [4], [59.6], [28.0 ($P = 0.14$)], [72.4], [34.5 ($P = 0.03$)],
  ))
]

With the clustered variance and the top three or four digits forced, the remaining scatter under $0^0 = 0$ is noise, and under $0^0 = 1$ it is marginal. Two items remain. Under $0^0 = 1$ the model is 12% low on average in both parities, at 3.0 standard deviations. Under $0^0 = 0$ base 19 has 0.67 times the model's rate of near-solutions; this looked like 4.6 standard errors with the naive variance and is 2.9 with the clustered one, one case among 42, so it is no longer a separate anomaly. Base 13 is high because its lengths are short and local factors of the kind in @sec-short-heuristic raise the count. @sec-model-anomalies collects the verdicts.

=== Why the integer digits are almost uniform

In the function-field world of @sec-worlds-ffield the model fails, because Frobenius makes the digits of $F$ strongly structured: whole positions are always zero, and zeros are 4 to 700 times more common than the model assumes. One can ask whether the integer digits of $F$ hide a similar structure. They do not, apart from the top.

#computation(id: "model-comp-int-zeros", title: [Zero digits of $S(c)$ in the integers], src: "24.6")[
  For 100,000 random $(b - 1)$-digit strings $c$ per base with a $(b - 1)$-digit weight, in bases 11 to 41 under $0^0 = 1$: the top two or three digits of $S(c)$ are almost never zero, or zero far more often than $1 slash b$. Below them, the rate of zero digits is $1 slash b$ within 3%, at the top and at the bottom positions alike.
]

The forced top digits move the integer predictions by a few percent only: they change the chance that the zero counts of $c$ and $S(c)$ match by less than 2%, raise the parity factor under $0^0 = 1$ by 2% to 4%, and lower the total by about 1% through the $b$-digit share #lib("24.6").

There is a second lesson in the comparison. In $FF_q [T]$ the near-solution check of the library first agreed with the census, but only because adding $(B - 1) g$ to a solution there gives a near-solution with the same class sums: the offsets mapped solutions to near-solutions one to one, so they were not independent draws. The library first argued that this cannot happen in the integers, because changing digits changes $F$ by $w(d_0 - j) - w(d_0) + w(d_1 + j) - w(d_1) != 0$. That argument overlooks rearrangements. Swapping two digits keeps the multiset, so it keeps $F$, and it moves $n$ by a multiple of $b - 1$. So a multiset can be a near-solution at several offsets at once, and two thirds of the integer near-solutions share their multiset with another offset (@sec-model-evidence). The integer offsets are therefore weaker evidence than independent draws, but they are not copies of the solutions as in $FF_q [T]$, and the test of @model-comp-spectrum stands with wider error bars.#footnote[Library section 24.6.3 calls an integer near-solution "a genuine second draw". Section 26.4 corrects this.]

#remark(id: "model-rem-blocks")[
  Some solutions contain a block that pays for itself, such as $(3, 3, 6, 6, 1)$ in base 13, where $13 dot P_((3,3,6,6))(13) = 3^3 + 3^3 + 6^6 + 6^6$ (@sec-cons-blocks). In the model a solution ends in such a self-paying tail with probability $T_m (b) slash b^m$, where $T_m (b)$ counts the $m$-digit tails that pay for themselves. Under $0^0 = 1$, $T_1 (b) = 1$ (the digit 1) and $T_2 (b)$ is the number of 2-digit solutions, usually 0. So the block route is a share of about $1 slash b$ of the solutions, already counted. In bases 2 to 43 under $0^0 = 1$, 2 of the 59 solutions with at least 4 digits have an exact split at the last digit, against 3.38 expected #lib("22.5").
]

== Near-solutions as evidence <sec-model-evidence>

Almost every "chance" verdict in this document rests on near-solutions: a count at $D = 0$ is compared with its mean over many offsets in the class of 0. The library first treated the offsets as independent draws. They are not, and the reason is elementary.

#lemma(id: "model-lem-swap", title: "Swap lemma", src: "26.1")[
  Let $n$ and $n'$ have the same digit multiset in base $b$, both without a leading zero. Then $F(n') = F(n)$ and
  $ n' - F(n') = (n - F(n)) + (n' - n), quad n' - n equiv 0 med (mod b - 1). $
  If $n'$ is $n$ with the digits $x$ at position $i$ and $y$ at position $j > i$ exchanged, then $n' - n = (x - y)(b^j - b^i) = (x - y) b^i (b - 1) R_(j - i)$, where $R_s = 1 + b + dots + b^(s - 1)$. For the last two digits this is $(x - y)(b - 1)$.
]
#proof[
  $F$ depends only on the multiset. Every power of $b$ is 1 modulo $b - 1$, so a number is congruent to its digit sum, and the two digit sums agree. For the transposition only positions $i$ and $j$ change.
]

So the near-solutions of one multiset form a _cluster_: a multiset $c$ is a near-solution at every offset $D = n' - S(c)$ for which some arrangement $n'$ of $c$ puts $D$ in the offset set. A single coincidence, a weight $S(c)$ close to one of its own arrangements, is counted at several offsets. The same holds in every positional world where $F$ depends only on the multiset: negative bases, factorions, the factorial system and the Pisot base #lib("26.1").

#proposition(id: "model-prop-design", title: "What the clusters change", src: "26.1")[
  Assume that distinct multisets are independent, as the model does. Then the count $N_D$ at one offset is still Poisson, up to clumps such as twins at that offset, and the mean $lambda$ of the counts over $J$ offsets is still unbiased. But the total $T$ over the offsets has variance $phi E T$ with the _design effect_ $phi = E[K^2] slash E[K]$, where $K$ is the number of offsets at which a near-solution's multiset appears. So $J$ offsets are worth only about $J slash phi$ independent ones. Finally $N_0$ and $T$ are positively correlated, because a solution and its rearrangements lie in one cluster.
]

The design effect is the familiar quantity of cluster sampling (@app-prob): a survey that interviews whole households learns less than one that interviews the same number of unrelated people.

#computation(id: "model-comp-design", title: "Design effects", src: ("26.2", "26.3"))[
  Integer bases 12 to 26, offsets $2 j(b - 1)$, $j = 1, dots, 60$, numbers with at least $b - 6$ digits. Between 43% and 88% of the near-solutions share their multiset with another offset. The design effect is 1.5 to 3.5 (pooled 2.48 under $0^0 = 0$ and 2.14 under $0^0 = 1$), so 60 offsets are worth 26 to 29 independent ones. The partner pairs sit at the moves of @model-lem-swap: 43% at a swap of the last two digits, 20% at positions 0 and 2, 18% at positions 1 and 2. Of the 52 solutions in these bases, 29 have a rearrangement that is a near-solution in the window. A simple count of the expected partners under uniform bottom digits predicts the design effect within a few percent under $0^0 = 1$. Factorions, negative bases, near-2-cycles and the Pisot bases have design effects of 1.6 to 6.4; offset families with steps divisible by many small numbers have none.
]

A better offset family avoids the problem. Choose offsets $D = k(b - 1)$ such that no two differ by the move of a single transposition. This _transposition-free_ family cuts the shared share to about 15%, keeps the mean within 4%, and is worth about 51 of 60 offsets. For a single count $N_0$ against its offsets, the right P value mixes the Poisson law over the uncertainty of $lambda$, with the variance inflated by $phi$ and with the clumps at one offset (twins, factorion triples) built in #lib("26.3").

=== Every verdict revisited

The library recomputed every P value that rests on offsets. @tab-model-verdicts lists the main ones. The pattern is clear. Verdicts about $D = 0$ barely move, because the Poisson noise of a single count of 3 to 60 dominates the calibration error. What moves are statements about the precision of $lambda$ itself: per-base comparisons with the model and comparisons between offset families.

#tablefig(caption: [Verdicts that rest on near-solutions, with the naive and the clustered calibration #lib("26.4").], id: "tab-model-verdicts")[
  #btable(columns: 4, align: (left, right, right, left), size: 8.5pt,
    [statement], [old], [new], [verdict],
    [integers, 4 groups of @model-comp-spectrum], [$P$ 0.30 to 0.43], [0.31 to 0.43], [unchanged],
    [empty base 19, union mean 1.9], [0.15], [0.15], [unchanged],
    [no $b$-digit solution under $0^0 = 1$, 0 against 1.30], [0.27], [0.27], [unchanged],
    [per-base scatter, chi-square on 21 bases], [97, 96], [41, 43], [half an artefact],
    [base 19 near-solutions, $0^0 = 0$], [$z = -4.6$], [$z = -2.9$], [one case of 42],
    [model 12% low under $0^0 = 1$], [$z = 4.4$], [$z = 3.0$], [weaker, survives],
    [odd-base factorions, per family], [0.003 to 0.02], [0.004 to 0.025], [unchanged],
    [factorions, combined with fresh bases], [about 0.05], [about 0.09], [weaker],
    [factorions, after the choice of 16 groups], [about 0.1], [0.13], [unchanged],
    [5-digit excess, bases 13 to 99, window calibration], [0.0047], [0.0055], [unchanged],
    [the same after the choice of 10 cells], [0.015], [0.018], [unchanged],
    [negative bases, last digit kept, 42 against 52], [0.09], [0.11], [unchanged],
    [negative multiples of 3, 10 against 17.3], [0.044], [0.056], [unchanged],
    [step-$b$ offsets against step offsets, negative bases], [about 4 SD], [2.9 SD], [weaker],
    [2-cycles in even bases, 2 against 5.25], [0.10], [0.11], [unchanged],
  )
]

=== A pooled test across worlds

Each world of @ch-worlds with a near-solution calibration gives one comparison of $D = 0$ with its offsets. Pooling them tests whether $D = 0$ is special anywhere.

#computation(id: "model-comp-pooled", title: "Eight worlds pooled", src: "26.5")[
  Integers, odd-base and even-base factorions, negative bases, rational bases, the Pisot bases, Eisenstein bases and 2-cycles: 284 solutions against 297 to 304 expected from their offsets. The worlds disagree more than chance allows: the heterogeneity statistic is 17.2 to 23.3 on 7 degrees of freedom ($P = 0.002$ to 0.016), depending on the Pisot calibration. Two worlds drive it, the odd-base factorions (ratio 0.33) and the Pisot bases (ratio 1.34 to 1.56). Without them the other six fit one common ratio of 0.91, with $P = 0.60$ for heterogeneity.
]

So outside two named worlds there is no sign that $D = 0$ is special. The odd-base factorions are the shortfall found after looking at 16 groups (@sec-model-anomalies). The Pisot excess is mostly a calibration fault: for even $x$ the offsets $j x$ mix two classes modulo $2x$, and the defect spectrum peaks near $D = 0$; against a local calibration in the right class, 25 solutions against 14.8 expected has $P approx 0.05$ (@sec-worlds-pisot) #lib("26.6").

=== Do the low digits of $F$ mix?

One can ask the model's assumption directly. Draw random strings $c$ whose weight has the right length, remove from $c$ the top three digits of $F(c)$, and ask whether the low digits of $F(c)$ have exactly the remaining copies of each value, compared with random low digits.

#computation(id: "model-comp-mixing", title: "A mixing statistic", src: "26.8")[
  The low digits of $F(c)$ agree with $c$ at the rate of random digits within 1.6% per value in the integers (base 20), in base $-20$, for factorions and in the factorial system, and within 3.7% in the Pisot base $x = 6$. $FF_5 [T]$ is the one world with a clear excess, 2.2% to 3.4% per value.
]

The statistic does not follow the model's error. It flags $FF_q [T]$ with the same sign under both conventions, where the model error changes sign, and it misses the factorial failure, which sits in the top digits. Both places where the model fails have one narrow cause, the top digits in the factorial system and the zero count in $FF_q [T]$ under $0^0 = 1$, and an average over all digit values dilutes both. The negative answer still confirms the picture of this chapter: apart from the top, the integer digits of $F$ look random.

== A Poisson limit theorem <sec-model-poisson>

The data say that the number of solutions in a base looks like a Poisson draw. In the model this can be proved, with the dependencies between solutions built in. The proof uses the Chen-Stein idea in its simplest form; @app-prob has the background.

=== The coupled model

To state a joint law for both conventions, the model must say how the events depend on each other. Split a multiset $c$ into its counts $c_0$, $c_1$ of zeros and ones and its upper part $u = (c_2, dots, c_(b-1))$. Put $V(u) = sum_(x >= 2) c_x x^x$. Then $F_m (c) = V(u) + c_1 + m c_0$.

#definition(id: "model-def-coupled", title: "Coupled model", src: "13.2")[
  For each upper part $u$, let $Y_u$ be a random integer with as many digits as $V(u)$: uniform in the basic version, and uniform on the integers of that length congruent to $V(u)$ modulo $b - 1$ in the refined version. The $Y_u$ are independent. The multiset $c$ is a model solution under convention $m$ if the digits of $Y_u + c_1 + m c_0$ form $c$.
]

The model replaces the large number $V(u)$ by a random number of the same length and, in the refined version, the same residue. It keeps the exact additions of the small digits. So three dependencies are exact: twins under $0^0 = 0$, the shared zero-free solutions, and the common residue of all completions of one upper part.

Fix a minimal length $ell >= 6$. An index $alpha$ is a multiset with $ell <= k <= b$ and at least two digits above 1, together with a convention, where the two conventions are one index when $c_0 = 0$. The condition on the upper part leaves out the self-paying families $(x, 0, dots, 0, 1)$, which have tiny mass in the model. The _cluster_ of an index is the set of indices with the same upper part. Indices in different clusters are independent.

#lemma(id: "model-lem-twins", title: "Twins are the only coupling", src: "13.2")[
  If two distinct indices in one cluster are both model solutions, then both belong to convention 0 (or are shared), and one string is the other plus 1, with last digits 0 and 1.
]
#sketch[
  The two strings are $s = Y_u + j$ and $s' = Y_u + j'$ with $|j - j'| <= b$, and they have the same upper part. A length change would force many digits $b - 1$ into one of them and change the upper part, so the lengths agree. Then compare digit sums: adding $delta > 0$ with $kappa$ carries changes the digit sum by $"ds"(delta) - kappa(b - 1)$, and $"ds"(delta) <= delta$ with equality only for $delta < b$. If both are of convention 0, the digit sum changes by exactly the change in the number of ones, which forces $delta = plus.minus 1$ and no carry: a twin pair. If one is of convention 1 with $c'_0 >= 1$ zeros, the same computation makes $c'_0$ a positive multiple of $b - 1$, so the string has at most one nonzero digit, which is excluded. Two type-1 indices have $delta = 0$.
]

#theorem(id: "thm-poisson", title: "Poisson approximation", src: "13.2")[
  Let $lambda_s$, $lambda_0$, $lambda_1$ be the expected numbers of shared, convention-0-only and convention-1-only model solutions, and let $Z_s$, $Z_0$, $Z_1$ be independent Poisson variables with these means. Then
  $ d_"TV" ((N_0, N_1), (Z_s + Z_0, Z_s + Z_1)) <= 2 b_1 + b_2, $
  where $b_1 = sum_u sigma_u^2$ is the sum over clusters of the squared expected cluster counts, and $b_2 = 2 E[T]$ with $T$ the number of model solutions under convention 0 that end in 0. For $ell = ceil(b slash 2)$ and $b >= 12$, the basic coupled model gives
  $ d_"TV" <= 14.2 slash b + 16 b^2 (b + 1) ell! slash b^ell = O(1 slash b). $
  The refined model gives the same with $14.2 kappa slash b$ in the first term and an extra factor $b - 1$ in the second term, under Assumption R below.
]
#sketch[
  Compare the family of indicators $X_alpha$ with independent Poisson variables $Z_alpha$ of the same means; the counts $(N_0, N_1)$ are sums of these. Clusters are independent in both families, and total variation is subadditive over independent blocks, so it suffices to bound one cluster. Inside a cluster, compare $X$ first with independent Bernoulli variables $B_alpha$, then $B$ with $Z$. Le Cam's inequality gives $d_"TV" (B, Z) <= sum p_alpha^2 <= sigma_u^2$. For $X$ against $B$, split the probabilities by the number of ones in the outcome vector: the outcomes with at least two ones have probability at most $P(K >= 2) + sigma_u^2 slash 2$, where $K$ is the number of solutions in the cluster, and the outcomes with zero or one ones differ by at most $E[K(K - 1)] + sigma_u^2$ in total. Summing over clusters, $sum E[K(K-1)]$ is the expected number of ordered pairs of solutions in one cluster, and by @model-lem-twins these are the twin pairs, so the sum is $2 E[T]$. The error terms come from two estimates. A cluster has at most $2(b + 1)$ relevant shifts $j$, and each has probability at most $2 D! slash b^(D - 1)$ to produce the upper part, which gives $sigma_u <= 4 b (b + 1) ell! slash b^ell$. And a convention-0 solution ending in 0 has its last digit fixed, which costs a factor $1 slash b$, while the chance that the other digits fit is summable over the lengths; this gives $E[T] <= 7.1 slash b$.
]

#heuristic(id: "model-assump-r", title: "Assumption R", src: ("13.2", "5.3"))[
  There is a constant $kappa$ such that for every length $k$ and every residue $r$, among uniform strings of $k - 1$ digits whose weight has $k$ digits, the share with $sum c_x (x^x - x) equiv r med (mod b - 1)$ is at most $kappa slash (b - 1)$.
]

Assumption R is about the residues of $x^x$, not about the model's randomness. It is the same assumption that gives the factor 1 for odd primes in @model-heur-parity. In odd bases the prime 2 forces $kappa >= 2$. A proof with some constant $kappa$ is open; the residues of $x^x - x$ modulo $3^e$ and $5^e$ are thin (@sec-short-coverings), which shows where uniformity can fail.

=== The correlation of the two conventions

Under the theorem, $(N_0, N_1)$ is approximately the bivariate Poisson pair $(Z_s + Z_0, Z_s + Z_1)$. Within one base its correlation is $rho(b) = lambda_s slash sqrt((lambda_s + lambda_0)(lambda_s + lambda_1))$. In the large-base limit a model solution is zero-free with probability tending to $e^(-1)$, so with the parity factors:

#heuristic(id: "model-heur-corr", title: "Shared solutions in the limit", src: "13.2")[
  #align(center, btable(columns: 7, align: (left,) + (right,) * 6,
    [], [$lambda_s$], [$lambda_0$], [$lambda_1$], [$E N_0$], [$E N_1$], [$rho$],
    [even base], [$e^(-1) = 0.368$], [0.632], [0.632], [1], [1], [0.368],
    [odd base], [$2 e^(-1) = 0.736$], [1.264], [0.399], [2], [1.135], [0.488],
  ))
]

In odd bases zero-free strings meet the parity rule of $0^0 = 1$ automatically, so they keep the factor 2, and the shared share rises. The library's correlation of 0.56 is pooled over bases 10 to 41, so it has two sources: shared solutions within a base, and the parity of the base, which lifts both means in odd bases. Drawing the 32 pairs from the bivariate Poisson laws with each base's own means, 200,000 times, gives a mean sample correlation of 0.47, with 5% to 95% range 0.19 to 0.71. A correlation of at least 0.563 has probability 0.30. So the observed 0.56 is an ordinary draw #lib("13.2").

== Empty bases <sec-model-empty>

A base is empty if it has no nontrivial solution under either convention. Bases 19, 27 and 35 are the only empty bases from 3 to 41, and base 43 has solutions.

#heuristic(id: "model-heur-empty", title: "The emptiness law", src: "9.7")[
  Let $E_0$ and $E_1$ be the expected numbers of solutions under the two conventions and $E_s$ the expected number of zero-free solutions, which count under both. If solutions occur independently, a base is empty with probability $exp(-(E_0 + E_1 - E_s))$. For bases 10 to 41 this is 14% to 18% for even bases and 4% to 9% for odd bases; at base 40, 17% and 8%.
]

The law holds in the perturbed worlds of @sec-model-tests.#footnote[The library quotes two versions of these rates. Sections 7.4 and 9.7 give 17% and 8% at base 40, with all lengths of a finite base. Section 4.5 gives 20% and 9%, the limits as $b -> infinity$ of the coupled model (@sec-model-poisson), where the short lengths no longer add solutions. The numbers in @model-heur-empty are the finite-base ones.] Odd bases are rarely empty because the parity effect doubles $E_0$. If the model is right, about one base in eight near base 40 is empty, and about one in seven in the large-base limit, so infinitely many bases are empty.

#computation(id: "model-comp-empty", title: "Empty bases in the data", src: ("9.7", "11.2"))[
  Bases 10 to 41: the model expects 2.62 empty even bases and 1.13 empty odd bases. The data have 0 and 3 (19, 27, 35). With each base's own spectrum $lambda_m (b)$ from @sec-model-defects, bases 12 to 32 expect 11.6 bases with no long solution under one convention or the other and have 11; even bases have fewer than expected, odd bases more.
]

The chance of no empty even base among 10 to 41 is 0.057 under the model, and base 44, also even, has a solution. The per-base spectra put the deficit in perspective: the total over both parities is normal, the residue modulo $b$ is the one residue the offsets do not match, and offsets $D = 2 j b(b - 1)$ that also match it predict slightly fewer solutions, not more. So no mechanism tied to $D = 0$ is visible, and the even-base deficit counts as chance.

Can one prove that infinitely many bases are empty? The library argues that the tools in this document cannot #lib("8.5"). Showing that one base is empty is a finite computation. But a congruence modulo $q$ removes only a fixed share of candidates, about $1 slash q$ of all numbers satisfy $n equiv F(n) med (mod q)$, and almost all of those are not solutions. The constructions of @ch-constructions only show that bases have solutions. And in the model each base is empty with probability about 20% (even) or 9% (odd) in the large-base limit, independently of the others; a proof would have to control these chance events in infinitely many bases at once. The opposite statement, that every large base has a solution, is equally far out of reach, and the model says it is false.

What can be said for certain is short. A base has a solution when one of the families applies: under $0^0 = 0$, every perfect power with a self-paying digit (@thm-self-paying); under both conventions, every base of a 2-digit solution (@thm-two-digit). These families cover few bases. For example, 55 bases up to $10^9$ have a 2-digit solution under $0^0 = 0$ #lib("9.7").

== Length against base <sec-model-window>

Write $J = b - k$ for a $k$-digit solution in base $b$. @thm-length gives $J >= 0$, and @heur-length-law says that $J$ is usually 1 or 2.

#computation(id: "model-comp-J", title: [The law of $J$ in the data], src: "9.9")[
  Nontrivial solutions in bases 10 to 41, by $J = b - k$:
  #align(center, btable(columns: 7, align: (left,) + (right,) * 6,
    [], [$J = 0$], [1], [2], [3], [4 to 9], [12 or more],
    [$0^0 = 0$], [2], [30], [10], [7], [8], [9],
    [$0^0 = 1$], [0], [30], [8], [6], [6], [6],
  ))
]

The solutions with a large $J$ are short: under $0^0 = 1$ they are the short coincidences of @ch-short, such as 3435 in base 10 with $J = 6$.

=== The bump beyond $ln b$

The limit law says that the expected number with $J >= j$ falls like $e^(-(j-1))$. At finite $b$, @tab-model-length-law shows values about three times the limit once $J$ passes $ln b$. The cause is the largest usable digit. A digit $x$ can appear in a $k$-digit solution only if $x^x < b^k$ (@thm-digit-bound). Now $(b - J + 1)^(b - J + 1) approx b^(b - J + 1) e^(-(J - 1))$, which drops below $b^(b - J)$ once $J > ln b + 1$. From then on a digit above $k$ becomes possible and adds solutions; after that the decay is again about $e^(-1)$ per step. So the expected number of solutions in base $b$ with $J >= j$ is $C e^(-j)$ with a bounded $C$, and with $j = ln b + a ln ln b$ it is about $C slash (b (ln b)^a)$.

=== The window

#conjecture(id: "conj-window", title: "Length window", src: "10.5")[
  Under $0^0 = 1$ and for every $epsilon > 0$:
  - only finitely many solutions with $k >= 3$ digits, apart from algebraic families such as those of @thm-binomial, lie in a base $b > k + ln k + (1 + epsilon) ln ln k$;
  - infinitely many lie in a base $b > k + ln k + (1 - epsilon) ln ln k$.
]

The reason is the pair of Borel-Cantelli lemmas (@app-prob). The expected number of solutions in base $b$ with $J > ln b + a ln ln b$ is about $C slash (b (ln b)^a)$. The sum over $b$ is finite for $a > 1$, so by the first lemma only finitely many bases have such a solution. It is infinite for $a <= 1$, and in the model the bases are independent, so by the second lemma infinitely many do. This is the same law as for the longest run of heads in $n$ coin flips, which is $log_2 n + O(log log n)$.

The library first stated a cruder window, $b <= k + (1 + epsilon) ln k$, and drew from it that each length has only finitely many solutions under $0^0 = 1$. The binomial families of @thm-every-length-m1 refute that: they give infinitely many solutions of every length $k >= 3$, in bases far above $k$, for an algebraic reason the model cannot see. Hence the exception for algebraic families in the conjecture.

#computation(id: "model-comp-window", title: "Exceptions to the window", src: "10.5")[
  Solutions under $0^0 = 1$ with $k >= 3$ and $J > ln b + 2$:
  #align(center, btable(columns: 4, align: (left, left, right, right),
    [region], [digits], [expected (model)], [observed],
    [bases 10 to 41 and 43, every length], [3 to 5], [0.96], [5],
    [], [6 to 10], [0.86], [0],
    [], [11 or more], [1.21], [2],
    [bases 44 to 127, up to 30 digits], [3 to 5], [0.05], [2],
    [], [11 or more], [0.00], [1],
    [bases 128 to 5000], [3 to 5], [0.01], [2],
  ))
]

The long exceptions agree with the model: 3 observed against about 1.2 expected, and one of the three lies in base 64, which has self-paying digits. The short exceptions do not: 9 against 1.0. That is expected, because the per-base model is the wrong tool for short strings. For a short string the base is the root of a polynomial (@thm-one-base), and the right question is whether that root is an integer. @sec-short-heuristic develops that heuristic. It explains the short solutions in the searched ranges, but it too misses the algebraic families.

For a fixed large length $k$, the model puts a $k$-digit solution in base $k$ with probability 8%, $k + 1$ with 55%, $k + 2$ with 23%, and so on. The expected number of bases with a $k$-digit solution is about 1, so a length has no base with probability about $e^(-1) = 37%$ and two or more with probability about 26%. Under $0^0 = 1$, 7 of the 29 lengths from 2 to 30 have no solution in any base up to 127, which is 24% #lib("3.4"). The missing lengths are missing only near the length: the binomial families supply every length in astronomically large bases.

== Cycles of $n |-> F(n)$ <sec-model-cycles>

Solutions are the fixed points of $n |-> F(n)$. The other cycles of this map are a natural second test, because a random mapping has a known number of cycles of each length.

#proposition(id: "model-prop-cycles", title: "Cycles live on multisets", src: "15.1")[
  Let $cal(M)_b$ be the set of digit multisets with 1 to $b$ digits and at least one nonzero digit. The map $c |-> (text("multiset of") S(c))$ sends $cal(M)_b$ into itself, and its cycles correspond one to one to the cycles of $n |-> F(n)$ on the integers $n >= 1$.
]
#proof[
  A multiset with at most $b$ digits has $S(c) <= b(b - 1)^(b-1) < b^b$, so $S(c)$ has at most $b$ digits, and it has a nonzero digit because $S(c) >= 1$. $F$ depends only on the multiset, so a cycle of integers gives a cycle of multisets of the same length. Two members of an integer cycle with the same multiset have the same image, and a cycle is a bijection on its members, so they are equal. Conversely, a multiset cycle gives the cycle of the integers $S(c)$.
]

$|cal(M)_b| = binom(2b, b) - b - 1$,#footnote[The multisets with at most $b$ digits over the values $0, dots, b - 1$ number $binom(2b, b)$, counting the empty one. Removing the empty multiset and the $b$ multisets made of zeros only leaves $binom(2b, b) - b - 1$.] so a full census is a walk over about $4^b slash sqrt(pi b)$ points. The engine walks each multiset once, with 2 bits of state per multiset; base 17 takes 670 seconds per convention, and base 18 about an hour #lib("15.1", "23.3").

The parity invariant of @thm-parity-invariant splits the map in odd bases under $0^0 = 0$: even numbers map to even numbers and odd ones to odd ones. A map from a finite nonempty set to itself has a cycle, so every odd base has a cycle of even numbers, and so a cycle besides the fixed point 1 #lib("15.1").

=== A random mapping with the invariant

A uniform random mapping on $N$ points has about Poisson$(1 slash L)$ cycles of length $L$ #cite(<flajolet-odlyzko1990>). The map $F$ is not uniform: the length of $S(c)$ and its residue modulo $b - 1$ are fixed by $c$. The class-lumped model keeps exactly this information. A class is a pair $K = (k, r)$: the $k$-digit multisets with digit sum $r$ modulo $b - 1$. In the model the image of $c$ is a random multiset of the class of $S(c)$, weighted by the number of strings with that multiset. Let $M$ be the matrix of class transitions.

#proposition(id: "model-prop-cycle-model", title: "Expected cycle counts", src: "15.1")[
  In the class-lumped model the expected number of cycles of length $L$ is $(1 slash L)$ times the sum, over $L$-tuples of distinct multisets, of the product of their transition probabilities. Up to the terms with a repeated multiset this is $(1 slash L) "tr"(M^L)$.
]

The spectrum of $M$ explains the parity effect for cycles. In odd bases under $0^0 = 0$, $M$ splits into an even and an odd block, the eigenvalue 1 has multiplicity 2, and $E_L approx 2 slash L$. Under $0^0 = 1$ the parity flips with the parity of the number of zeros; $E[(-1)^z] = (1 - 2 slash b)^k approx e^(-2)$, so $M$ has the eigenvalues 1 and about $e^(-2)$, and $E_L approx (1 + e^(-2 L)) slash L$. For $L = 1$ this is the factor $1 + e^(-2)$ of @model-heur-parity, seen from a new side.

#computation(id: "model-comp-cycles", title: "Cycles in bases 3 to 18", src: ("15.1", "23.3"))[
  Cycles of length 2 in bases 4 to 18 against the class-lumped model:
  #align(center, btable(columns: 5, align: (left, right, right, right, right),
    [group], [2-cycles], [model $E_2$], [$P(X <= "obs")$], [near-2-cycles per offset],
    [even, $0^0 = 0$], [2], [4.02], [0.24], [5.25],
    [even, $0^0 = 1$], [4], [4.30], [0.57], [4.97],
    [odd, $0^0 = 0$], [6], [7.23], [0.42], [8.32],
    [odd, $0^0 = 1$], [4], [3.88], [0.65], [3.92],
  ))
  The total number of cycles of all lengths in bases 3 to 17 matches the model in all four groups (for example 92 against 94.4 in odd bases under $0^0 = 0$). Fixed points are in excess by a factor 1.4 to 1.8, because of the constructions and the small bases.
]

=== The image of $F$

A random mapping also predicts how many points are hit. The image of $F$ is much smaller than that prediction.

#proposition(id: "model-prop-image", title: "Coincident sums", src: "26.7")[
  The image of the multiset map is the same under both conventions. Under $0^0 = 0$, multisets that differ only in their zeros have the same weight; under $0^0 = 1$, multisets that differ only in the split of $c_0 + c_1$ have the same weight.
]
#proof[
  Under $0^0 = 0$ a zero weighs nothing, and under $0^0 = 1$ zeros and ones both weigh 1. So under both conventions the image is the set of multisets of $S_0 (e)$ for the zero-free multisets $e$ of 1 to $b$ digits.
]

#computation(id: "model-comp-image", title: "The image share", src: "26.7")[
  The share of multisets with at least one preimage is 0.21 in base 10 and falls to 0.14 in base 16. The class-weighted random mapping predicts 0.38 to 0.31. Counting the distinct weights, not the multisets, closes 55% to 66% of the gap, and keeping the true top three digits of each weight closes about two thirds of the rest. The in-degrees are overdispersed: variance-to-mean 3.6 to 6.3 against 2.3 to 3.8 in the model.
]

So the forced top digits show up once more: the weights $S(c)$ share their leading digits far more than random integers do, and their multisets collide. The cycle counts above are not affected much, because they depend on the trace of the class matrix, not on the image.

An early observation said that every odd base from 3 to 11 has a 2-cycle under $0^0 = 0$ and no even base from 4 to 10 does. That is the parity doubling of the invariant plus chance: bases 13 and 15 have no 2-cycle, base 16 has one, base 18 has one. The deficit in even bases was tested with near-2-cycles, $F(F(n)) = n - j(b - 1)$, which keep every residue the map preserves. They come at the normal rate, 5.25 per offset against 4.02 in the model, so there is no second invariant #lib("23.3").

== Anomalies and how they were resolved <sec-model-anomalies>

A model tested on many groups of data will show a few deviations by chance. The library found several, and each one taught something. Before going through them, one statistical point.

#remark(id: "model-rem-look-elsewhere", title: "The look-elsewhere effect")[
  A deviation found by looking at the data is weaker evidence than its P value suggests. If you split the data into 14 groups and pick the most extreme one, a P value of 0.02 for that group is not surprising: the chance that at least one of 14 independent groups reaches 0.02 is $1 - 0.98^14 approx 0.25$. So the library corrects each P value for the number of groups it looked at, and it values fresh data, collected after a pattern was noticed, far above old data. A pattern that weakens in fresh data was probably chance.
]

/ The $(b-1)$-digit excess: In bases 10 to 38 under $0^0 = 1$, solutions with $b - 1$ digits were 1.6 times as common as the refined model predicts: 27 against 17.3, with $P = 0.019$ #lib("5.5"). But this was the most extreme of about 14 groups, so the corrected chance was about 23%. Correlation tests found nothing: the top 10 digits and the bottom 8 digits of $S(c)$ fit the multiset no more often than random digits do. In fresh bases 39 to 43 the excess continued weakly (5 against 2.45, $P = 0.10$). The resolution came from the perturbed weights of @sec-model-tests: over all lengths from $b - 6$ to $b$, the true counts fit the model, 16 against 14.9 in bases 16 to 28 and 17 against 14.6 in bases 29 to 41 #lib("9.6"). The excess at $b - 1$ digits is a fluctuation in how the solutions spread over the lengths; their total is normal.

/ Empty bases $equiv 3 (mod 8)$: Bases 19, 27 and 35 are all $equiv 3 med (mod 8)$, and so is 11, which has solutions. Three empty bases among the four such bases from 11 to 35 has probability about $10^(-3)$ in the model. But the residue class was noticed after the data, and among all 15 odd bases from 11 to 39 three empty ones has probability about 6%. Base 43, the next base $equiv 3 med (mod 8)$, has a solution #lib("4.5", "8.5").

/ Missing $b$-digit solutions: No base from 3 to 45 has a $b$-digit solution under $0^0 = 1$, against 3.6 expected in the refined model. This was the original conjecture of the library: no $b$-digit solutions at all. Under $0^0 = 0$ it is false, with bases 15 and 16. The defect spectrum showed that the model overestimates this length. Restricted to exactly $b$ digits, the offsets in bases 10 to 30 predict 1.30 solutions under each convention, against 2.33 and 1.74 from the model #lib("11.2"). The cause is the forced top digits. A $b$-digit sum needs at least three copies of $b - 1$, its leading digit is then 1 and the next one is about $0.10 b$, and these digits must also lie in the multiset, whose counts are depressed by the three copies of $b - 1$. The exact correction for the top one to three digits is 0.6 to 0.91 in bases 16 to 30, and it shrinks like $1 slash b$. With the spectrum's calibration, no $b$-digit solution under $0^0 = 1$ in bases 10 to 30 has probability 0.27. So the model still predicts a $b$-digit solution under $0^0 = 1$ in about 8% of large bases, and the search has simply not reached one.

/ The even-base empty deficit: No even base from 10 to 41 is empty, against 2.62 expected ($P = 0.057$). @sec-model-empty explains why it counts as chance.

/ Factorions in odd bases: With the weights $x!$, long factorions are rare in odd bases: 3 and 4 against about 11.9 per convention in bases 14 to 36. Offsets that keep every residue up to $b + 1$ and modulo $b^3$ give normal near-factorion counts, so no congruence explains it. Fresh odd bases 37 to 47 give 3 per convention against 6.2. With the clustered calibration of @sec-model-evidence the combined evidence has $P approx 0.09$, and 0.13 after the choice among 16 groups. The library counts it as an unexplained fluctuation (@sec-worlds-weights).

/ Base 19: The empty base 19 also has few near-solutions under $0^0 = 0$, 0.67 times the model's rate. With the naive variance this was 4.6 standard errors, a real anomaly. With the clustered variance it is 2.9, one case among 42 bases, and no longer a separate anomaly #lib("26.4").

Some deviations remain open. Each is a question in @sec-open-list.

- Under $0^0 = 1$ the per-base rate of near-solutions is 12% above the refined model, in odd and even bases alike. It survives the clustered calibration at 3.0 standard deviations #q(70).
- Base 19 is low in its near-solutions, now 2.9 standard errors #q(68). The question has lost most of its basis.
- The long solutions under $0^0 = 0$ in bases 12 to 41 contain fewer zero digits than the model predicts: 29 against 42.5, about 2.1 standard deviations. The forced top digits account for 2 to 4 of the 13.5. This is the one place where the integer data lean the way the function-field world does (@sec-worlds-ffield) #q(71).
- The model's per-base predictions seemed to scatter about 20% beyond sampling error. With the clustered variance and the top digits forced, the scatter is noise under $0^0 = 0$ and marginal under $0^0 = 1$ ($P = 0.03$) #q(44).
- In even Pisot bases, offsets $j x$ with even $j$ carry 1.4 to 2.4 times as many near-solutions as those with odd $j$ under $0^0 = 0$. The identity behind this class factor modulo $2x$ is unknown #lib("26.6").
