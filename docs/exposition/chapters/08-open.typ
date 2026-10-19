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
    [Are large short solutions family members?], st("conjecture"), [positions and linear families classified; the rest needs one more coincidence], [@open-families],
    [Is $(1, 6, 46666)$ the next 3-digit solution?], st("open"), [next family member (proven); none in bases 905 to $10^(3301)$], [@open-next-three],
    [At most two 3-digit solutions per base?], st("open"), [at most 30 outside a sparse set of bases (proven); at most two up to $10^(3301)$], [@open-two-three-digit],
    [Does every length occur?], st("proven"), [yes, under both conventions], [@sec-cons-binomial],
    [Is $N_0(b)$ bounded?], st("proven"), [no], [@thm-many-m0],
    [Is $N_1(b)$ bounded?], st("open"), [unknown; constructions give at most 2 in the bases searched], [@open-n1],
    [Infinitely many bases without solutions?], st("open"), [model: about 1 base in 8], [@open-empty],
    [A $b$-digit solution under $0^0 = 1$?], st("open"), [none in bases 3 to 45; model expects some], [@open-bdigit],
    [Bases with two 2-digit solutions under $0^0 = 1$], st("proven"), [only base 3], [@thm-two-two-digit],
    [$b(b + x) = x^x + 1$ only for $x = 3, 7$?], st("open"), [proven for prime powers and $x <= 4 dot 10^9$; abc implies finitely many], [@cor-x-x],
    [$b(b + x) = x^n + 1$ with $n >= 4$], st("open"), [only $(7, 7)$ known; finite under abc], [@sec-dio-exponents],
    [Count of solutions per base], st("heuristic"), [Poisson with mean about 1 per convention, doubled in odd bases under $0^0 = 0$], [@sec-model-poisson],
    [Length shares in the basic model], st("proven"), [8.0%, 55.2%, 23.3%, ... with error $O(1 slash b)$], [@thm-length-shares],
    [Assumption R], st("open"), [false for short lengths as first stated; proven by computation for bases 12 to 6000], [@open-assumption-r],
    [$k(B) = omega(B - 1)$ in $FF_q [T]$?], st("open"), [proven with a good factor, for $e <= 10$ and every census base; at most one more always], [@open-ffield],
    [Excess of $(b-1)$-digit solutions], st("heuristic"), [resolved: chance; the totals fit], [@sec-model-anomalies],
    [Empty bases $equiv 3 med (mod 8)$], st("computed"), [resolved: base 43 has a solution], [@sec-model-anomalies],
    [Excess of 5-digit solutions in bases 13 to 99], st("heuristic"), [unexplained fluctuation, $P approx 0.015$], [@sec-short-heuristic],
    [Factorion shortfall in odd bases], st("heuristic"), [unexplained fluctuation; $P approx 0.13$ after the choice among 16 groups], [@sec-worlds-weights],
    [Excess of solutions in Pisot bases], st("heuristic"), [mostly calibration: a class modulo $2x$; $P approx 0.05$ after recalibration], [@open-pisot-class],
    [Are near-solutions at different offsets independent?], st("proven"), [no: rearrangements link them; means stay unbiased, variances grow 1.5 to 3.5 times], [@sec-model-defects],
    [Do all worlds share one rate of solutions to near-solutions?], st("computed"), [six of eight do (ratio 0.91); odd-base factorions and Pisot bases differ], [@sec-worlds-universal],
    [A search faster than $1.9^b$], st("heuristic"), [exact: open; with a 1 to 3% miss rate about $1.75^b$; tree searches need $1.638^b$ in the model], [@sec-search-entropy],
    [Can another order of the tree beat $1.638^b$?], st("proven"), [no: every order, fixed or adaptive, in the model], [@open-fast-search],
    [Certificates of emptiness], st("proven"), [in an interval oracle model, at least the widest level of the exact tree, up to a small factor], [@open-certificates],
    [Constraint solvers], st("computed"), [exact but grow 1.95 to 2.3 per base, worse than the tree], [@open-fast-search],
    [Polynomial-time search], st("open"), [as hard to settle as P versus NP], [@sec-search-complexity],
    [Arbitrary weights], st("proven"), [NP-complete, counting \#P-complete], [@thm-gen-npc],
    [Galois groups of $Q_s$], st("proven"), [$S_(k-1)$ generically; classified for $k = 4, 5$], [@sec-short-galois],
    [Integers with three bases under $0^0 = 1$], st("open"), [none known], [@open-three-bases],
    [Lengths in base $-1 + i$], st("proven"), [exactly $equiv 1, 4 med (mod 8)$], [@worlds-minus1i],
    [Finitely many solutions in the factorial system?], st("open"), [only 1, 2, 4, 5 below $34!$; a top-digit model leaves 14 of 31 lengths open and finds the empty census ordinary], [@open-factorial],
    [Why the model misses in $FF_q [T]$], st("heuristic"), [Frobenius blocks and the $0^0 = 1$ channel proven; a model that keeps the blocks closes most of the $0^0 = 0$ gap], [@sec-worlds-ffield],
  )
]

== Problems <sec-open-list>

=== Structure under $0^0 = 1$

Under $0^0 = 0$ the zero digits cost nothing, and constructions are easy:
self-paying digits combine freely, and every length and every count occurs.
Under $0^0 = 1$ every zero costs 1, and the known structure is thin: the
2-digit families, two linear families of power identities, and a few
chains of power identities. @sec-cons-binomial describes the families.

#conjecture(id: "open-families", title: [Large short solutions are family members], src: ("25.1", "22.3"))[
  Under $0^0 = 1$ and for each $k >= 3$, all but finitely many $k$-digit
  solutions are members of the two linear families: the binomial families
  of @thm-binomial, and the family $(c^j, 0, dots, 0, x)$ with
  $x = c^(j c^j) + j - 1$. Moreover every $k$-digit solution in a base
  above the largest base of the complete list (904, 20, 48, 9 and 9 for
  $k = 3, dots, 7$) is such a member. (#q(64))
]

Much of #q(64) is now settled (#lib("25.1")). In every power identity
$Q_s(r) = lambda A(r)^j - W$, where $W$ is the weight of the large digits,
the last digit is one of the large digits (Theorem 25.2, proven). With $A$
linear the members are the binomial families and a second family with
$e = 0$, for example $(8, 0, 0, 16777218)$ in base
$16777218^5592406 slash 2$; it gives infinitely many solutions of every
length $k >= 4$ and the smallest known ones with 4, 5 and 6 digits
(Theorems 25.4 and 25.5, proven). Nonlinear $A$, decomposable $P_s$,
products, Aurifeuillian factors, several large digits and self-paying
digits with a paying tail each need one more Diophantine coincidence
(Proposition 25.6), and a census of all small prefixes finds no member of
any of them. For 3 digits with two digits at most $B$ and the third at least
$2B + 4$ the classification is complete (Theorem 25.7). The evidence for
the conjecture is the complete lists of @sec-short-lists, which hold no
solution above these bases up to $10^(51)$, $10^(186)$, $10^(30.9)$ and
$10^(11)$ for 3 to 6 digits, extended to $10^(3301)$ for 3 digits, and the
root heuristic of @sec-short-heuristic, which leaves less than $10^(-74)$
expected generic 3-digit solutions beyond the list. Under $0^0 = 0$ the
conjecture fails: self-paying digits and swaps give further families.

#problem(id: "open-nonlinear", title: [Nonlinear identity families], src: "25.1")[
  Is there an identity family with nonlinear $A$, that is, a parametrized
  $A$ for which $A(b) = x^(x slash j)$ is solvable by structure?
]

Proposition 25.6 reduces this to values of polynomials at perfect powers.
For each fixed $A$ the Schinzel-Tijdeman theorem bounds the exponent, so a
family would need $A$ to vary.

#problem(id: "open-next-three", title: [The next 3-digit solution], src: ("25.2", "22.3"))[
  Prove that $(1, 6, 46666)$ in base $46666^23333 - 3$, about
  $10^(108942)$, is the next 3-digit solution under $0^0 = 1$ after
  $(1, 7, 1)$ in base 904. (#q(65))
]

What is known (#lib("25.2")):
- proven: $(1, 6, 46666)$ is the next member of the families after
  $(1, 2, 6)$, and the only 3-digit solution in its base (Theorem 25.10);
- computed: no 3-digit solution lies in a base from 905 to $10^(3301)$,
  and below $46666^23333 - 3$ every other 3-digit solution has two digits
  above 200 and one above 2000 (Theorem 25.11, a sieve with 108 primes over
  $1.36 dot 10^10$ strings);
- heuristic: the strings left open add an expected $10^(-3294)$ solutions.

The open part is the strings with two digits in $[201, 46666]$ and one
above 2000. They are generic Pell-type equations with two large digits
(@sec-short-square). A sieve over all of them has about $10^14$ strings; a
sieve over pairs of large digits, with the third digit fixed by size,
could cut this to about $10^10$ tests and close the gap.

#problem(id: "open-n1", title: [Is $N_1(b)$ bounded?], src: ("8.4", "15.5"))[
  Is there a constant $C$ such that every base has at most $C$ solutions
  under $0^0 = 1$?
]

Under $0^0 = 0$ the answer is no (@thm-many-m0). Under $0^0 = 1$ a
self-paying digit replaced by 0 leaves a near-solution with
$F(n) = n + 1$, so a construction like @thm-many-m0 needs near-solutions of
every small defect in one base. The chain-and-cycle construction of power
identities (#lib("15.5")) gives at most 2 solutions in every base $r^t$
with $r <= 40$ not a perfect power and $t <= 300$, the range searched. The model says that the count is a Poisson
variable with mean about 1, which has no bound, but a large count would be
a chance event in a single base. A chain whose top lands within the number
of available self-paying digits of the zero count it needs would give three
or more solutions; bases $r^t$ with $r$ in ${2, 3, 5, 6}$ and $t$ up to
$10^4$ with many divisors are the natural place to look (#q(88)).

#problem(id: "open-three-bases", title: [Three bases], src: ("15.6", "18.3"))[
  Is there an integer that is a solution under $0^0 = 1$ in three
  different bases? (#q(39))
]

Under $0^0 = 0$ the number of bases is unbounded: $2^2048 + 1$ has 26. Under
$0^0 = 1$ an integer has at most two 2-digit representations, and every
other representation of an integer $a^a + c^c$ with two 2-digit bases has a
rigid shape (#lib("18.3")). None exists among the 2,117 integers with a
2-digit representation with digits up to 90.

#problem(id: "open-two-three-digit", title: [Two 3-digit solutions per base], src: ("25.3", "18.2"))[
  Does every base have at most two 3-digit solutions under $0^0 = 1$?
  (#q(50))
]

Base 4 has two, $(1, 3, 1)$ and $(3, 1, 3)$, and every other base up to
$10^(3301)$ has at most one (computed, Theorem 25.11). Partial results
(#lib("25.3"), proven): the largest digits of the 3-digit solutions of one
base take at most two consecutive values; every base has at most 30
three-digit solutions, except at most 13 bases near $M^((M-1) slash 2)$ for
each $M$, which have at most $2M + 24$ (Theorem 25.15); a base has at most
one family member, and a base with a member has at most three 3-digit
solutions (Propositions 25.16 and 25.17). The method of @thm-two-two-digit
fails at the shape $(M, u, v)$, where a base near $M^((M-1) slash 2)$ gives
an equation in two free digits. A proof that this shape has at most two
solutions per base would give an absolute bound near 26, and with more
care perhaps 2. See also @sec-short-two-three.

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

The model says yes: about 17% of even and 8% of odd bases near base 40 are
empty, and 20% and 9% in the large-base limit. The
data agree: bases 19, 27 and 35 are the empty ones up to 41 (base 43 has solutions), and each base's
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

#problem(id: "open-assumption-r", title: [Assumption R], src: ("13.2", "29.3"))[
  Prove that $rho(b) < 1 - 3 ln b slash b$ for every base $b > 6000$, where
  $rho(b)$ is the largest normalized exponential sum of $x^x - x$ modulo
  $b - 1$ over the digit ranges $[0, L)$ with $L >= b slash 2$. (#q(54),
  #q(80), #q(112), #q(113))
]

This is the only gap in the refined version of @thm-poisson, and it is the
factor 1 for odd primes in @sec-model-refined. @model-thm-rho reduces
Assumption R to this one number per base, and a computation proves it for
$12 <= b <= 6000$ (@model-cor-r-small). The computed $rho(b)$ tends to
0.7638, the 3-adic limit of @model-prop-rho3, and @model-conj-rho predicts
$rho(b) <= 0.77$ from base 100 on. Small prime factors of $b - 1$ are
handled by Gauss sums (@model-prop-small-p). The hard case is a prime
$p = b - 1$, where the digits see each residue of $x$ once. There the sums
$sum_(x < p) e(h (x^x - x) slash p)$ show square-root cancellation in the
data, but no bound below $p$ for a single $h$ is known. Over every odd prime
power dividing $b - 1$ for $b <= 20,000$, the Poisson rate of the residues
is at least 0.2143, and at least 0.2308 from base 10 on.

The length shares of the basic model, once listed here, are now a theorem
(@thm-length-shares). Its first-order correction $c_j slash b$ is known in
the basic model but not in the refined one (#q(114)).

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
    its solutions? (#q(68)) With clustered near-solutions it is 2.9
    standard errors below the model with forced top digits, one case of 42,
    so this is no longer a separate anomaly.
  + Why is the model about 12% low under $0^0 = 1$ in both parities of the
    base? (#q(70)) The excess survives the corrected variance at 3.0
    standard deviations.
  + Do the long solutions under $0^0 = 0$ really have fewer zero digits than
    the model, 29 against 42.5 in bases 12 to 41? (#q(71))
  + In negative bases, offsets that keep the last digit give 6% to 23%
    fewer near-solutions, about 2.9 standard deviations with clustering.
    Which digits of $F mod b$ cause this?
  + Narcissistic numbers with $d >= 6$ exceed the refined model by 18% in
    even bases, mostly bases 8 and 10. Do bases 16, 18 and 20 show the
    same? (#q(87))
]

Each of these is a deviation of one to three standard deviations. The
per-base scatter of about 20% that the library first reported is half an
artefact: near-solutions at different offsets share multisets, and the
sample variance of the offset means overstated their precision
(#lib("26.4")). With the corrected variance and the top three or four digits
of the sum forced, the scatter is noise under $0^0 = 0$ ($P = 0.09$ to 0.14)
and marginal under $0^0 = 1$ ($P = 0.03$). A model that also fixes the
bottom digits and adds local factors for short lengths is the natural next
step.

#problem(id: "open-near-solutions", title: [Near-solutions as a calibration], src: "26.1")[
  Find a closed form of the design effect, the factor by which clusters of
  rearranged near-solutions inflate the variance of an offset mean, for
  factorions, negative bases and Pisot bases. Rerun the rational and
  Eisenstein offsets with the strings kept, so that their design effect is
  measured rather than assumed.
]

For integer bases a heuristic based on swaps of the bottom four or five
digits predicts the design effect within a few percent (#lib("26.1")).
Offsets with no transposition between them, or with steps divisible by many
small numbers, avoid the clusters and keep the mean.

#problem(id: "open-pisot-class", title: [The class modulo $2x$ in Pisot bases], src: "26.6")[
  In the Pisot bases $epsilon_x$ with even $x$, under $0^0 = 0$, offsets
  $j x$ with even $j$ carry 1.4 to 2.4 times as many near-solutions as
  offsets with odd $j$. Which identity causes this? (#q(74))
]

The congruence of @worlds-pisot-mod2x ties the parity of $(N - sum d_i) slash x$
to the arrangement of the digits, not to their multiset, so it does not
give the factor by itself. With the offsets in the class modulo $2x$ and a
local calibration, the Pisot excess has $P approx 0.05$
(@sec-worlds-pisot).

#problem(id: "open-cycles", title: [Cycles of $n |-> F(n)$], src: ("15.1", "23.3"))[
  The full census of cycles stops at base 17; base 18 was searched only for
  2-cycles. Do the cycle counts keep following
  the class-lumped random-mapping model, and are the zero-free cycles, which
  count under both conventions, more common than the model's share?
]

The image of the map is far from that of a random mapping: 14% to 21% of
the multisets of bases 10 to 16 are hit, against 31% to 38% for the
weighted random mapping. Exact coincidences between sums and the forced top
digits explain most of the gap (#lib("26.7"), computed). A model of the
image that forces the top digits and counts the coincidences exactly is
open.

=== Search and complexity

#problem(id: "open-fast-search", title: [A fast exact search], src: ("6.4", "8.1", "10.4", "27.2"))[
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

Several routes are now closed (#lib("27"), #lib("28")):
- the entropy bound holds for every order of revealing digit counts, fixed
  or chosen node by node, so the top-down order is optimal among trees
  (Theorem 27.2, proven in the model); bottom-up and random orders peak
  near $3.6^b$;
- in bases $2^k$ the bottom digits of the sum are fixed only once the
  counts of all odd digits are known, so a check of bottom digits prunes
  nothing in a top-down tree, and orders that reveal the odd counts early
  lose (Proposition 27.8, Corollary 27.9);
- the constraint solvers CP-SAT and CaDiCaL are exact but grow 1.95 to 2.3
  per base, as fast as the tree or faster, at $10^4$ to $10^5$ times its
  cost (computed, bases 8 to 20);
- the inexact search gains a constant factor: a corrected law for the
  z-score rule visits 1.1 to 1.3 times fewer nodes at the same miss rate,
  and a GPU runs it 2.6 to 2.9 times faster than 8 CPU threads.

#problem(id: "open-certificates", title: [Certificates of emptiness], src: "27.3")[
  In an oracle model where a query reveals the interval of the sum for a
  partial assignment of digit counts, every certificate that a base has no
  solution needs at least $N_k$ queries for every level $k$, a number at
  least 0.86 times the widest level of the exact tree in bases 5 to 21
  (Theorem 27.5, proven). Prove that this share stays bounded below as $b$
  grows, which would give a lower bound $2^(b - O(log b))$ in this model.
  What can an oracle that also reveals low digits do?
]

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
    to 12, and push those lengths to bases $10^4$ to $10^5$. (#q(29)) A
    first step is done: the 8-digit list is complete for bases up to
    23,364 and the 7-digit list up to $10^(7.2)$ (#lib("19.1")).
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
$x = 15$ on, in computations that assume the generalized Riemann
hypothesis, so the class group alone cannot close the case
(#lib("20.5")). The weak abc inequality $c < K "rad"(a b c)^(2 - delta)$
implies that there are finitely many solutions; an effective form of it,
together with the sieve, would finish the proof (@app-abc).

#problem(id: "open-n5", title: [The exponent $n = 5$], src: "18.1")[
  Find all integer points on the genus 2 curve $b^2 + x b = x^5 + 1$.
]

No solution has $x <= 10^(10)$. The Jacobian has analytic rank 3, so its
Mordell-Weil rank is probably 3, larger than the genus. If so, Chabauty's
method does not apply (@app-curves). The
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
  the $x$ that are not prime powers.
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
fails there (@sec-worlds-factorial). A model that keeps the true top digits
of the sum explains the failure: it leaves 14 of the 31 lengths up to 33
open, closes every length without near-solutions, and makes the empty
census an ordinary outcome (@worlds-fact-open). It expects about 0.3
solutions for $34 <= L <= 40$ and 2.5 up to $L = 100$
(@worlds-fact-predict). A census to $L = 40$ with integers wider than 128
bits is the next test. Why $L = 13$ has the largest model mean but few
near-solutions (#q(116)), and how to sample the model beyond $L = 50$
(#q(117)), are open.

#problem(id: "open-ffield", title: [A formula for $FF_q [T]$], src: ("21.1", "24.5"))[
  Find a formula, or a good heuristic, for the average number of solutions
  over all bases of degree $e >= 3$ in $FF_q [T]$. Is $k(B) = omega(B - 1)$
  always (@worlds-ff-kB-conj)? Which values of the leading coefficient pass the test of
  @worlds-ff-short for $e = 3$ and $q equiv 2 med (mod 3)$? Prove that
  $T^q$ has no zero digit in a non-square base of degree 2 with two roots of
  $B - 1$. (#q(111), #q(115))
]

@worlds-ff-kB proves $k(B) = omega(B - 1)$ whenever $B - 1$ has a factor of
degree prime to $e - 1$, and for every $e <= 10$; the first open case is
$e = 11$ with factors of degrees 5 and 6. The block model of
@worlds-ff-blockcomp, which keeps the Frobenius blocks and randomizes the
rest, predicts the census within 3% to 9% in total. It still misses the
bases where $B - 1$ has a repeated factor, and a formula would have to
explain those.

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
  form a fractal tile, not an interval. (#q(89))
]

For base $-4 + i$ a disk around each tile could serve as the prefix test.
The model puts 83% of its expectation at 34 digits, so such a test would
complete the Gaussian census one base further.

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
