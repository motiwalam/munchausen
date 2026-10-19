#import "../template.typ": *

= Open problems <ch-open>

This chapter collects what is not known. The first section gives the status
of the main questions in one table. The second states the open problems, by
theme, with the evidence for each and with what a solution would need. The
questions are numbered as in the library's list,
`docs/library/questions.md`, so that #q(64) means question 64 there.

Several open problems run into the same barrier. A proof that some
coincidence between powers never happens, for infinitely many cases at
once, is beyond current methods. @sec-short-square explains the barrier for
short solutions, and @sec-search-complexity for algorithms. It is worth
keeping in mind when judging which problems are realistic.

== Status <sec-open-status>

#let st(s) = status-badge(s)
#tablefig(caption: [The main questions and their status.], id: "open-tab-status")[
  #btable(
    columns: 4, size: 8.5pt,
    align: (left, left, left, left),
    [question], [status], [answer], [where],
    [Does every base have finitely many solutions?], st("proven"), [yes: at most $b$ digits], [@thm-length],
    [Finitely many $k$-digit solutions under $0^0 = 1$, $k >= 3$?], st("proven"), [no: binomial families give infinitely many], [@thm-every-length-m1],
    [Does every length occur?], st("proven"), [yes, under both conventions], [@sec-cons-binomial],
    [Is $N_0(b)$ bounded?], st("proven"), [no], [@thm-many-m0],
    [Is $N_1(b)$ bounded?], st("open"), [unknown; constructions give at most 2], [@open-n1],
    [Infinitely many bases without solutions?], st("open"), [model: about 1 base in 8], [@open-empty],
    [A $b$-digit solution under $0^0 = 1$?], st("open"), [none in bases 3 to 45; model expects some], [@open-bdigit],
    [Bases with two 2-digit solutions under $0^0 = 1$], st("proven"), [only base 3], [@thm-two-two-digit],
    [$b(b + x) = x^x + 1$ only for $x = 3, 7$?], st("open"), [proven for prime powers and $x <= 4 dot 10^9$; abc implies it], [@cor-x-x],
    [$b(b + x) = x^n + 1$ with $n >= 4$], st("open"), [only $(7, 7)$ known; finite under abc], [@sec-dio-exponents],
    [Count of solutions per base], st("heuristic"), [Poisson with mean about 1 per convention, doubled in odd bases under $0^0 = 0$], [@sec-model-poisson],
    [Excess of $(b-1)$-digit solutions], st("heuristic"), [resolved: chance; the totals fit], [@sec-model-anomalies],
    [Empty bases $equiv 3 med (mod 8)$], st("computed"), [resolved: base 43 has a solution], [@sec-model-anomalies],
    [Excess of 5-digit solutions in bases 13 to 99], st("heuristic"), [unexplained fluctuation, $P approx 0.015$], [@sec-short-heuristic],
    [Factorion shortfall in odd bases], st("heuristic"), [unexplained fluctuation, $P approx 0.05$], [@sec-worlds-weights],
    [A search faster than $1.9^b$], st("heuristic"), [exact: open; with a 1 to 3% miss rate about $1.75^b$; tree searches need $1.638^b$ in the model], [@sec-search-entropy],
    [Polynomial-time search], st("open"), [as hard to settle as P versus NP], [@sec-search-complexity],
    [Arbitrary weights], st("proven"), [NP-complete, counting \#P-complete], [@thm-gen-npc],
    [Galois groups of $Q_s$], st("proven"), [$S_(k-1)$ generically; classified for $k = 4, 5$], [@sec-short-galois],
    [Integers with three bases under $0^0 = 1$], st("open"), [none known], [@open-three-bases],
    [Lengths in base $-1 + i$], st("proven"), [exactly $equiv 1, 4 med (mod 8)$], [@worlds-minus1i],
    [Finitely many solutions in the factorial system?], st("open"), [only 1, 2, 4, 5 below $34!$], [@open-factorial],
    [Why the model misses in $FF_q [T]$], st("proven"), [Frobenius blocks and the zero count], [@sec-worlds-ffield],
  )
]

== Problems <sec-open-list>

=== Structure under $0^0 = 1$

Under $0^0 = 0$ the zero digits cost nothing, and constructions are easy:
self-paying digits combine freely, and every length and every count occurs.
Under $0^0 = 1$ every zero costs 1, and the known structure is thin: the
2-digit families, the binomial families, a few chains of power identities.

#problem(id: "open-families", title: [Are large short solutions algebraic?], src: ("22.3", "22.4"))[
  Is every short solution under $0^0 = 1$ beyond some size a member of an
  algebraic family, such as the binomial families of @thm-binomial? Are
  there other identity families, for example with $p x^x$ a $j$-th power for
  a leading digit $p$ that is not a $j$-th power, or with two large digits?
  (#q(64))
]

Evidence: the complete lists of @sec-short-lists stop at bases near
$10^(186)$ for 4 digits and $10^(51.5)$ for 3 digits. The root heuristic
of @sec-short-heuristic puts the expected number of further generic
solutions at $10^(-74)$ for 3 digits, and the identities are exactly what
it cannot see. A classification of the identities would turn the heuristic
into a precise conjecture: finitely many solutions outside the families.

#problem(id: "open-next-three", title: [The next 3-digit solution], src: "22.3")[
  Is $(1, 6, 46666)$ in base $46666^23333 - 3$ the next 3-digit solution
  under $0^0 = 1$ after $(1, 7, 1)$ in base 904? (#q(65))
]

A proof needs the finiteness of the Pell-type equations of
@sec-short-square up to bases near $10^108942$. The obstacle is that the
base and the exponent of $x^x$ vary together, a situation no published
method handles.

#problem(id: "open-n1", title: [Is $N_1(b)$ bounded?], src: ("8.4", "15.5"))[
  Is there a constant $C$ such that every base has at most $C$ solutions
  under $0^0 = 1$?
]

Under $0^0 = 0$ the answer is no (@thm-many-m0). Under $0^0 = 1$ a
self-paying digit replaced by 0 leaves a near-solution with
$F(n) = n + 1$, so a construction like @thm-many-m0 needs near-solutions of
every small defect in one base. The chain-and-cycle construction of power
identities (#lib("15.5")) gives at most 2 solutions in every base $r^t$
with $r <= 40$ and $t <= 300$. The model says that the count is a Poisson
variable with mean about 1, which has no bound, but a large count would be
a chance event in a single base.

#problem(id: "open-three-bases", title: [Three bases], src: ("15.6", "18.3"))[
  Is there an integer that is a solution under $0^0 = 1$ in three
  different bases? (#q(39))
]

Under $0^0 = 0$ the number of bases is unbounded: $2^2048 + 1$ has 26. Under
$0^0 = 1$ an integer has at most two 2-digit representations, and every
other representation of an integer $a^a + c^c$ with two 2-digit bases has a
rigid shape (#lib("18.3")). None exists among the 2,117 integers with a
2-digit representation with digits up to 90.

#problem(id: "open-two-three-digit", title: [Two 3-digit solutions per base], src: "18.2")[
  Does every base have at most two 3-digit solutions under $0^0 = 1$?
  (#q(50))
]

Base 4 has two, $(1, 3, 1)$ and $(3, 1, 3)$, and every other base below
$10^(51)$ has at most one. The proof of @thm-two-two-digit for two digits
used elementary inequalities. For 3 digits the hard case is a leading
digit that is also the largest digit.

#problem(id: "open-cores", title: [Cores in perfect-power bases], src: "15.3")[
  Under $0^0 = 0$, is $(1, 3)$ in base 25 the only 2-digit core in a
  perfect-power base that is not a swap $(a, a^a)$? (#q(37))
]

The abc conjecture settles the case where one of $a^a$, $c^c$ is much
smaller than the other (@sec-dio-cores). The case $a^a approx c^c$ has four
large terms, and abc does not apply.

=== The model

#problem(id: "open-empty", title: [Infinitely many empty bases], src: ("8.5", "9.7", "11.2"))[
  Are there infinitely many bases without a solution under either
  convention?
]

The model says yes: about 17% of even and 8% of odd bases are empty. The
data agree: bases 19, 27 and 35 are the empty ones up to 43, and each base's
own near-solution spectrum predicts its chance of being empty. A proof would
have to exclude a coincidence in infinitely many bases at once. Congruences
remove only a fixed share of the candidates, and constructions only show that
bases have solutions. The opposite statement, that every large base has a
solution, is equally out of reach and false in the model.

#problem(id: "open-bdigit", title: [$b$-digit solutions under $0^0 = 1$], src: ("7.1", "8.6", "11.2"))[
  Does some base $b$ have a solution with $b$ digits under $0^0 = 1$?
]

Under $0^0 = 0$ bases 15 and 16 have one. Under $0^0 = 1$ none exists in
bases 3 to 45. The model expects a $b$-digit solution in about 8% of large
bases, but it overestimates this length at small $b$ because the top digits
of a $b$-digit sum are forced. The near-solution calibration expects 1.3
in bases 10 to 30, where 0 is observed ($P = 0.27$). So the evidence does
not support the original conjecture that none exists, and a search with
`--min-digits b` in bases near 50 is the natural test.

#problem(id: "open-assumption-r", title: [Assumption R], src: ("13.2", "5.3"))[
  Prove that the residues of $sum_x c_x (x^x - x)$ modulo the odd prime
  powers dividing $b - 1$ are spread evenly over the multisets whose sum has
  a given length, with an explicit constant. (#q(54))
]

This is the only gap in the refined version of @thm-poisson, and it is the
factor 1 for odd primes in @sec-model-refined. The 3-adic and 5-adic laws of
@sec-short-coverings show where uniformity can fail: modulo $3^e$ and $5^e$
the values of $x^x - x$ are thin.

#problem(id: "open-length-tail", title: [The length tail], src: "10.5")[
  Does the tail of the length law beyond $J = ln b + 1$, which supports
  @conj-window, appear in many perturbed worlds? (#q(56))
]

#problem(id: "open-model-details", title: [Second-order effects in the model], src: ("22.4", "23.5", "24.6"))[
  Several small deviations from the refined model are unexplained:
  + The base-by-base calibration of @sec-short-heuristic has not been
    applied to the 4-digit list or to the long solutions of bases 12 to 40.
    (#q(66))
  + Factorions: what could separate $D = 0$ from every small offset that
    keeps all residues up to $b + 1$ and modulo $b^3$? (#q(67))
  + Why is base 19 low in its near-solutions under $0^0 = 0$, not only in
    its solutions? (#q(68))
  + Why is the model about 12% low under $0^0 = 1$ in both parities of the
    base? (#q(70))
  + Do the long solutions under $0^0 = 0$ really have fewer zero digits than
    the model, 29 against 42.5 in bases 12 to 41? (#q(71))
  + In negative bases, offsets that keep the last digit give 10 to 25%
    fewer near-solutions. Which digits of $F mod b$ cause this?
]

Each of these is a deviation of one to three standard deviations, or a
residual scatter of about 20% between bases. The forced top digits explain
a third to a half of the scatter (#lib("23.5")). A model that also fixes the
bottom digits and adds local factors for short lengths is the natural next
step.

#problem(id: "open-cycles", title: [Cycles of $n |-> F(n)$], src: ("15.1", "23.3"))[
  The census of cycles stops at base 18. Do the cycle counts keep following
  the class-lumped random-mapping model, and are the zero-free cycles, which
  count under both conventions, more common than the model's share?
]

=== Search and complexity

#problem(id: "open-fast-search", title: [A fast exact search], src: ("6.4", "8.1", "10.4"))[
  Is there an exact search whose cost grows more slowly than about
  $1.9^b$? Is there one with polynomial cost?
]

The set of bases with a solution is a tally language in NP (@thm-np). A
proof that it is not in P would prove that NE differs from E, which is
stronger than P different from NP; a proof that it is NP-hard would prove
P = NP (@sec-search-complexity). So neither direction is provable with
current methods. Within the model, every tree search that walks the digits
from the top needs about $1.638^b$ nodes (@thm-entropy-bound), and a quantum
search could reach about $1.41^b$. A large classical gain needs a new source
of information about the low digits of $n$.

#problem(id: "open-hardness-long", title: [Hardness with long solutions], src: "13.1")[
  Is the problem with arbitrary weights still NP-complete on weight tables
  whose solutions must have at least $b - C$ digits, or at least $b slash 2$?
  (#q(55))
]

The hard instances of @thm-gen-npc have solutions with at most $b slash 2$
digits, while real solutions have about $b - 1$ digits.

#problem(id: "open-powers", title: [Powers as weights], src: ("13.1", "18.6"))[
  With weights $x^(e(x))$ and exponents in unary, is the problem NP-hard?
  (#q(40))
]

The reduction of @thm-gen-npc needs digits whose weights have a prescribed
base-$b$ expansion. With pure powers this forces exponents of size
$exp(c sqrt(k slash log k))$ for $k$ items, by linear forms in logarithms
(#lib("18.6")). A reduction would have to use long expansions, for example
the explicit digits of $(b - c)^e$.

#problem(id: "open-search-misc", title: [Two search projects], src: ("6", "19.1"))[
  + Compute the near-solution spectrum in one pass: widen the interval of
    the search tree by $W$ and check every offset $|D| <= W$ at the leaves.
    (#q(25))
  + Find where the tree search and the string sieve cross over for lengths 8
    to 12, and push those lengths to bases $10^4$ to $10^5$. (#q(29))
]

=== The Munchausen polynomial

#problem(id: "open-decomposition", title: [Reducibility comes from decompositions], src: "16.3")[
  For every $k$, is there a bound $F(s) <= C_k M^(c_k)$, with $M$ the largest
  digit, beyond which every factorization of $Q_s$ without a linear factor
  comes from a decomposition $P_s = G(h(r))$? (#q(33))
]

The statement is a theorem for $k = 5$ (@sec-short-galois). For $k = 6$ the
same elimination gives a curve of genus 1, and the integrality step becomes a
question of approximating $Z cos(2 pi slash 5)$ by rationals with bounded
denominator.

#problem(id: "open-coverings", title: [Which moduli coverings need], src: ("15.4", "20.2"))[
  Does every covering congruence that excludes a family of digit strings in
  every base use a modulus $q$ on which $x^x - x$ misses residues, that is a
  power of 2, 3 or 5? (#q(38))
]

Every covering found so far uses such a modulus, sometimes together with
others: the covering of $(2, 0, 1, 0, x)$ under $0^0 = 1$ uses 8, 11 and 25.

=== Exponential Diophantine equations

#problem(id: "open-x-x", title: [$b(b + x) = x^x + 1$ for composite $x$], src: ("16.2", "18.1", "20.5"))[
  Prove that $b(b + x) = x^x + 1$ has no solution with $x > 7$.
]

What is left is described in @cor-x-x: $x > 4 dot 10^9$ odd, composite, not
a prime power, with a mixed ideal whose class has order $d | x$ and
$x slash d < 3.3 dot 10^4 ln x$. Class orders with $d | x$ do occur, from
$x = 15$ on, so the class group alone cannot close the case
(#lib("20.5")). The weak abc inequality $c < K "rad"(a b c)^(2 - delta)$
would finish the proof together with the sieve (@app-abc).

#problem(id: "open-n5", title: [The exponent $n = 5$], src: "18.1")[
  Find all integer points on the genus 2 curve $b^2 + x b = x^5 + 1$.
]

No solution has $x <= 10^(10)$. The Jacobian has analytic rank 3, larger
than the genus, so Chabauty's method does not apply (@app-curves). The
problem is decidable with Baker's method for hyperelliptic curves and the
Mordell-Weil sieve, which needs a 2-descent and a saturated basis of the
Mordell-Weil group. More generally, is the set of $(x, n)$ with $n >= 4$
finite? Only $(7, 7)$ is known.

#problem(id: "open-even", title: [The even case], src: ("18.1", "20.3"))[
  Solve $b(b + x) = x^n + 1$ for $x equiv 0 med (mod 8)$ with an odd prime
  factor and odd $n >= 5$.
]

Here the 2-part of the ideal has exponent $a n - 2$, not a multiple of $n$,
and the linear form in logarithms has three terms. Matveev's theorem bounds
$n$ in terms of $x$ and a class order, but nothing bounds $x$ in terms of $n$
except in one pure configuration. No solution has $x <= 10^4$ (all $n$) or
$x <= 10^8$ ($n <= 15$).

#problem(id: "open-c3", title: [The families $(1, x, 2)$ and $(1, x, 3)$], src: "20.4")[
  Prove that $(1, x, 2)$ is never a solution under $0^0 = 1$, that is,
  that $b(b + x) = x^x + 3$ has no solution; and finish $(1, x, 3)$ for
  composite $x$.
]

No solution exists for $x <= 10^9$ in either family. For $(1, x, 3)$ the
method of @sec-dio-baker works for prime powers, because the ideal of norm
$x$ has an explicit generator. For $(1, x, 2)$ no such generator is known,
and the regulator of the quadratic order is not bounded by $log x$, so even
prime $x$ remains open.

=== Other number systems

#problem(id: "open-factorial", title: [The factorial number system], src: "21.5")[
  Does the factorial number system have finitely many solutions?
]

Only 1, 4, 5 under $0^0 = 0$ and 1, 2, 5 under $0^0 = 1$ exist below
$34!$. No length bound and no residue are available, and the windows model
fails there (@sec-worlds-factorial). A model that fixes the top digits from
the large counts, as the search tree does, and a search past $34!$ with
wider integers are the next steps.

#problem(id: "open-ffield", title: [A formula for $FF_q [T]$], src: ("21.1", "24.5"))[
  Find a formula, or a good heuristic, for the average number of solutions
  over all bases of degree $e >= 3$ in $FF_q [T]$. Is $k(B) = omega(B - 1)$
  always? Which values of the leading coefficient pass the test of
  @worlds-ff-short for $e = 3$ and $q equiv 2 med (mod 3)$? Prove that
  $T^q$ has no zero digit in a non-square base of degree 2 with two roots of
  $B - 1$.
]

#problem(id: "open-gauss-lengths", title: [Length runs in Gaussian bases], src: ("14.5", "23.4"))[
  Prove the runs of lengths of positive integers in base $-n + i$ for
  $n >= 2$. (#q(69))
]

For $n = 1$ the proof uses $beta^4 = -4$ (@worlds-minus1i). For $n >= 2$ no
power of $beta$ is real.

#problem(id: "open-worlds-searches", title: [Out-of-reach censuses], src: ("14.5", "21.2", "21.3"))[
  Complete the census of base $-4 + i$ past 22 digits, of base $-3 + omega$
  at 27 and 28 digits and of $-4 + omega$, and of the rational bases
  $11 slash 8$, $11 slash 10$ and $p >= 12$. Each needs a better pruning
  rule: in Gaussian and Eisenstein bases the numbers with fixed top digits
  form a fractal tile, not an interval.
]

#problem(id: "open-gauss-excess", title: [Base $-3 + i$], src: "14.5")[
  Base $-3 + i$ has four solutions under $0^0 = 1$ against 1.11 expected,
  three of them with 19 digits ($P = 0.026$). Is this chance?
]

=== Lengths without solutions

The binomial families give solutions of every length, so no length is
missing in all bases. The question that survives concerns bases near the
length.

#conjecture(id: "open-missing-lengths", title: [Missing lengths near the base], src: ("3.4", "11.4"))[
  Under $0^0 = 1$, every solution with 9, 18, 21, 22, 24, 26 or 28 digits
  belongs to an algebraic family such as the binomial families of
  @thm-binomial, and so lies in an astronomically large base.
]

No base up to 100,000 has a 9-digit solution, and no base up to 10,000 has
one with the other lengths (computed). The root heuristic puts the expected
number of 9-digit solutions in larger bases, outside algebraic families, at
$10^(-29)$. In bases up to 127, lengths 31 to 45 have not been surveyed
against the model's prediction that about 37% of long lengths are missing
(#q(18)).
