# Round 5: directions and questions

DRAFT. A reading of the whole library, chapters 1 to 24 and the questions 1
to 71, produced this file. Part A names seven broad directions that the
library has not explored or has only touched. Part B poses 18 concrete
questions, numbered 72 to 89, each raised by a result of a named chapter. The
last section groups 15 of them into three agent workloads.

The questions avoid the work already in progress: the identity families and
the 3-digit questions 64, 65 and 50, and the search performance work (the
`--zscore` rule with the forced-top-digit model, length windows, GPU
stacking).

A few leads come from quick runs by the questioner. Their scripts were
throwaway runs in a scratch directory and are not in the repo. Their numbers
are leads, not results.

## Part A. Directions

### A1. The self-power map `x -> x^x mod m`

The residues of `x^x` drive four separate results of the library: the parity
doubling (section 5.3), the sets `T(q)` and the coverings (Lemma 15.12,
Theorems 20.8 to 20.12), the prime powers in the `kdigit` sieve (section
19.1), and Assumption R, the one gap in the Poisson theorem of chapter 13.
All four were proven or measured from scratch. The self-power map has its own
literature, which the library never cites. Papers that I remember, and which
must be checked before use: Kurlberg, Luca and Shparlinski on the fixed
points of `x -> x^x mod p`; Balog, Broughan and Shparlinski on the number of
solutions of exponential congruences; Crocker and Somer on the residues of
`n^n`; Holden and Robinson on small cycles. Exponential sums of the form
`sum over x < N of e(h x^x / p)` are exactly what Assumption R needs when
`b - 1` has a large prime factor. A first project: collect the known bounds,
compute the sums for every `p = b - 1` prime up to `10^5`, and prove
Assumption R in the case where `b - 1` has no prime factor above `b^(1/2)`,
where the digits cover many full periods of `x mod p (p-1)`. The payoff is a
theorem: the residue factor law of chapter 21 ("the count factor follows the
identity modulus") would hold in the coupled model without assumption, for
every base. It does not speed up the exact search.

### A2. Why no method beats the tree, and what could

Theorem 10.1 proves a floor of about `1.638^b` for searches that reveal the
digit counts from the largest value down. Section 10.4 tries five other ideas
and finds that each one fails, and chapter 13 shows that any method that
treats the weights as an oracle meets NP-completeness. Two gaps remain
between these statements. First, Theorem 10.1 fixes the order in which counts
are revealed. Second, it bounds searches that find a solution with
probability `p`, not searches that certify that a base is empty, which is what
an exact search does. The natural setting for both is query complexity in a
random-oracle model. An algorithm may ask for the interval of `S(c)` for any
partial assignment of counts, in any order, and the low digits of `S(c)` are
random. In that model one can ask for the size of the smallest certificate of
emptiness, and whether it is the exact tree, which grows like `2^b`
(section 10.1). If the answer is yes, the library has its "reason why none
can": every classical method must use arithmetic of `x^x` that the oracle
hides, and chapters 11, 15 and 20 show how little of that exists. If the
answer is no, the certificate shows a new search. A second, empirical
project: encode one base as a constraint problem (positional digits with
carries, one-hot digits, the histogram constraint) and give it to a CDCL or
CP-SAT solver. Clause learning is resolution, not a tree walk, so Theorem
10.1 does not cover it. A measured growth rate on bases 10 to 24 would tell
whether learned nogoods cut across branches. This direction matters most for
the exact search: it decides whether to keep looking for a better method.

### A3. Branching processes and large deviations for the search tree

The library computes the growth of the exact tree (section 9.1), of its likely
part (section 10.1) and the law of the worst z-score on a solution path
(sections 9.5 and 10.3). Each computation is a separate formula. A
multitype branching process, with the type of a node given by its level, its
number of unknown positions and its free digit count, would give all of them
as one object. Its first moment is the node count per level, which
`tree_model.py` already sums. Its second moment and its tail give what the
library has never measured: the distribution of subtree sizes. That
distribution decides the work-unit split of `--journal` runs, the time
estimate for a long run such as base 49 for factorions, and the risk that one
unit takes most of the time. Large-deviation theory (Cramer, and the
entropy of section 10.1) gives the finite-`b` corrections that explain why the
measured growth is 1.89 and not 2. A first project: fit the per-unit node
counts in the journals of existing long runs, compare them with the
branching-process prediction, and derive the best unit depth as a function of
`b` and the number of threads. This helps the exact search by a constant
factor, through scheduling, and gives reliable time estimates.

### A4. A mixing criterion for the coincidence model

The model works in integer, negative, Gaussian, Eisenstein, rational and
Pisot bases, and for the weights `x^(x+t)` and `x^d`. It fails in the
factorial system (section 21.5.3) and, by a factor up to 40, in `F_q[T]`
under `0^0 = 1` (chapter 24). In both failures the cause is the same in
kind: the digits of `F(c)` are not independent of the multiset `c` beyond the
identity. In the factorial system large digits are tied to top positions. In
`F_q[T]` Frobenius builds the digits of `F` from `e` single digits
(Corollary 24.3). In the integers only the top 2 or 3 digits are forced
(Table 24.6.1). This suggests one statistic for every world: the information
that the digit histogram of `F(c)` carries about `c`, measured below the
forced top digits. Concretely, sample `c`, compute the histogram `h(F(c))`,
and compare the joint law of `(c, h(F(c)))` with the product law by a
chi-square or a mutual information, conditioned on the length. The model
error should be a function of this defect. A first project: compute it with
the existing engines for the integers, base -10, the factorial system,
`F_q[T]` with `(q, e) = (5, 3)` and the Pisot base `x = 4`, and plot it
against the measured model ratio. A positive result would turn the scattered
"why it works here and not there" remarks into one law, and would predict in
advance which new worlds the model can handle.

### A5. Additive structure of weight sums at the bottom

The model needs two input facts about random multisets: the residue of
`S(c) = sum c_x x^x` modulo the odd part of `b - 1` is spread out
(Assumption R), and the bottom digits of `S(c)` are uniform (Table 24.6.1,
measured). Both are statements about sums of a random number of copies of the
fixed integers `x^x`, and both can be proven by Fourier analysis on the
Poisson model: the characteristic function is
`exp(-sum over x of (1 - e(h x^x / q)))`. The same tool would address the
equidistribution that section 20.1.5 needs to push Theorem 20.3 past
`alpha = 1`, though there the counts are not random. Bases with a small
radical are a special case. In base `2^k` every even digit `x >= k L` has
`x^x == 0 (mod b^L)`, so the bottom `L` digits of `S(c)` depend only on the
odd digits and a few small even ones. That is the integer analog of the
Frobenius blocks of chapter 24, at the bottom instead of everywhere. A first
project: prove bottom-digit uniformity for `L` up to a power of `b` in the
Poisson model, and measure in bases 32, 64 and 128 how much a bottom-up check
on the odd counts prunes. Lead (computed, 40,000 random `(b-1)`-digit strings
per base and convention): the last-digit factor `E[b c_v / d]`, with
`v = S(c) mod b`, is 1.00 within 0.01 in all 18 bases from 10 to 64,
including 32, 48 and 64. So the last digit alone carries no correction.

### A6. The functional graph of `F` as a test of the model

Chapter 15 counts the cycles of `n -> F(n)` and compares them with a random
mapping that keeps the class of `S(c)` (Proposition 15.6). Cycles are a thin
slice of the graph. A random mapping also predicts the share of points in the
image (about `1 - 1/e` per class, with corrections for the class sizes), the
in-degree law, the tail lengths and the size of the largest tree. All of
these can be measured in the same pass of `dyn_cycles.rs` that visits every
multiset once. They test the model on about `4^b` events per base instead of
the one or two solutions, and they test it in the regime of short and medium
multisets, where the per-base model was never checked. A first project: add
image and in-degree counts to `dyn_cycles.rs` for bases 10 to 16 and compare
with the class-lumped model. A mismatch would locate a correlation between
`c` and the digits of `S(c)` that A4 could then measure.

### A7. Exponential Diophantine equations in families of fields

Chapters 16, 18 and 20 solve `b(b+x) = x^n + c` for prime powers `x` and
small `x`, and leave composite `x` with a non-principal ideal (Corollary
18.11) and `c = 3` with a large regulator (Proposition 20.29). The
obstacle is the same each time: the field `Q(sqrt(x^2 + 4c))` changes with
`x`, so Baker's method applies to one `x` at a time. Two general tools have
not been tried. One is the theory of integral points on the surface
`U^2 = 4 x^n + x^2 + 4c` with `(x, n)` both varying, through the results on
`y^2 = a x^n + c` that are uniform in `n` (Bennett, Bugeaud, Mignotte and
their coauthors). The other is the abc-type method of Proposition 18.13 made
effective in the weak form, which the library already showed suffices. This
direction is touched, not new, and it gives no speedup. I list it because
the binomial families of chapter 22 show that the short-solution problem is
now a question about which of these equations have polynomial solutions, and
a uniform method would serve questions 64 and 65 as well.

### Which directions help the exact search

A2 matters most: it either finds a method that is not a top-down tree or
explains why there is none. A3 gives a constant factor through scheduling and
reliable time estimates for long runs. A5 can prune from the bottom only in
bases with a small radical, so it helps special bases such as 64 and 128, not
base 100. A1, A4, A6 and A7 improve the theory and the predictions, not the
search.

## Part B. Questions

## Theme XI. Solutions against their near-solutions

### 72. A pooled test of `D = 0` against the near-solutions

In every world the library calibrates the solution count by near-solutions
`n = F(n) + D` with `D` in the class of 0. Taken together, are the solutions
an ordinary draw, or is `D = 0` systematically low?

Why: Each world was judged alone, and each verdict was "chance". Lead
(computed from the published tables): integers 63 against 59.9 (section 11.1);
odd-base factorions 7 against 21.4 (19.5); even-base factorions 21 against
21.4 (17.4); negative bases, offsets that keep the last digit, 42 against 52.0
(23.2); rational bases 67 against 75.9 (21.2); Pisot bases, twins removed,
55 against 39.8 (21.4); Eisenstein bases 6 against 4.5 (21.3); 2-cycles 16
against 22.5 (23.3). The sum is 277 against 297.3 (z = -1.2), but the eight
z-scores have a chi-square of about 21 on 7 degrees of freedom. The worlds
disagree with each other more than Poisson noise allows. Either the
calibrations have errors of their own (question 73), or some worlds have
structure at `D = 0` that the offsets lack.

Attack: Collect the observed counts and the calibrated means per base, not
per group, from the data files of chapters 11, 17, 19, 21 and 23. Fit one
common ratio `D = 0 / near` with a random effect per world. Report the
between-world variance and the worlds that drive it.

Kind: computation.

### 73. Near-solutions at different offsets are not independent

If `n = F(n) + D` and `n'` is `n` with two digits swapped, then
`n' = F(n') + D'` with `D' = D + (x - y)(b^i - b^j)`, a multiple of `b - 1`.
How strongly does this couple the offset counts that sections 11.1, 17.4,
19.5 and 23.1 use as independent draws?

Why: The swap identity is trivial (the multiset, hence `F`, does not change),
but the library never uses it. Swaps of the last two digits move `D` by
`(x - y)(b - 1)`, which is inside the offset window `j <= 120`. So one
coincidence (a multiset whose `S(c)` lies near one of its permutations) can
appear at several offsets. The mean count per offset stays unbiased, but the
spread of the offset totals is larger than Poisson, and statements such as
"30 of 30 offsets lie above `D = 0`" (section 19.5) overstate the evidence.
Lead (computed, `fast search --offset 2j(b-1)`, `j = 0..40`, lengths at least
`b - 6`): in bases 14, 16, 17 and 18, between 41% and 65% of the
near-solutions share their digit multiset with a near-solution at another
offset. The number of distinct multisets is 61% to 77% of the number of
near-solutions.

Attack: State the swap lemma. Rerun the offsets of section 11.1 for bases 12
to 24 with the strings printed, and group them by multiset. Recompute the
variance of the offset totals by multiset clusters, and redo the P values of
sections 11.2, 19.5 and 23.1 with the clustered variance.

Kind: proof (the lemma) and computation.

### 74. Why the Pisot bases exceed their near-solutions

In the Pisot bases `eps_x` (section 21.4), even `x` under `0^0 = 0` have 31
solutions against 15.9 from the near-solutions, and 24 after the 7 twin pairs
are removed. Odd `x` and `0^0 = 1` are also above. Is there a structure that
`D = 0` has and the offsets `j x` lack?

Why: This is the largest positive deviation in question 72 (z = +2.4 after
twins). The Pisot expansions have digits after the point, and the twin rule of
Proposition 21.13 has a second form at position -1 for `x = 1`. Other exact
moves may exist: a digit `x` must be followed by 0, so changing the last digit
can force a carry into position -1. If such moves pair solutions with
solutions but not near-solutions with near-solutions, they explain the excess.

Attack: List the 62 solutions of `analysis/data/r3t_pisot_search*.txt` with
their expansions. For each, look for another solution at distance at most
`2x` and record the digit change. Then run the offsets `j x` with
`r3t_pisot` and count the same pairs among near-solutions.

Kind: computation.

## Theme XII. Limits of search

### 75. The entropy bound for other orders

Theorem 10.1 bounds searches that reveal the counts from the largest digit
down. What does the same entropy argument give if the counts are revealed in
another order: smallest first, from the middle out, in a random order, or in
an order chosen node by node?

Why: The floor `1.638^b` is the only quantitative barrier in the library.
Section 10.4 argues that the leading digits are the only cheap
information, but no statement compares orders. If every order has
entropy at least `0.4933 b` at its widest level, the floor covers all trees
that reveal counts. If some order has a smaller peak entropy, it suggests a
new tree.

Attack: In `analysis/exponents.py`, write the law of the node above a planted
solution for a general order as a product over the revealed values of the
Poisson laws of their counts, given what the interval reveals. Evaluate the
peak entropy for the four orders at `b = 40, 100, 1000`.

Kind: computation.

### 76. Certificates of emptiness in an oracle model

In a model where the low digits of `S(c)` are random and an algorithm may ask
for the interval of `S(c)` under any partial assignment of counts, what is the
smallest certificate that a base has no solution? Is it of the order of the
exact tree, `2^(b - o(b))`?

Why: An exact search certifies emptiness, and Theorem 10.1 says nothing about
certificates. Section 9.1 argues that every node of the exact tree is
consistent with all the information the search has. A theorem would turn this
into a lower bound for every exact algorithm that uses only the oracle, and so
would say precisely which arithmetic of `x^x` a faster method must use. Since
section 8.1 rules out unconditional lower bounds for the real problem, the
oracle model is where such a statement can be proven.

Attack: Define the model. For `b` from 5 to 9, with random weights of the size
of `x^x`, compute the smallest refutation by integer programming over the
nodes of all orders, and compare it with the exact tree. Then try to prove the
lower bound by an adversary argument: the adversary keeps the low digits
undecided until an interval forces them.

Kind: proof.

### 77. A constraint solver as a search that is not a tree

Encode "base `b` has a solution with `d` digits" as a constraint problem and
solve it with a CDCL or CP-SAT solver. How does the solver time grow with
`b`, against 1.89 per base for `fast`?

Why: Theorem 10.1 covers trees that reveal counts. A solver with clause
learning can reuse a refutation across branches, which no tree in the library
does. A growth rate below 1.64 would break the model's floor for a natural
class of methods. A rate near 2 or above would be evidence that learned
clauses do not cut across the coincidence structure.

Attack: Use the positional form
`sum over x of c_x digit_i(x^x) + carry_i = n_i + b carry_(i+1)`, one-hot
variables for each `n_i`, and `c_v = #{i : n_i = v}`. Install `ortools` in a
virtual environment in the scratch directory (it is not on the machine). Solve
bases 8 to 22 at `d = b - 1` under `0^0 = 1`, check the answers against
`output/`, and fit the growth. Keep each run under 10 minutes and 2 threads.

Kind: computation.

### 78. The law of subtree sizes

What is the distribution of the node counts of the work units of an exact
run? Is its tail heavy enough that one unit can dominate a base?

Why: Long runs (base 47 for factorions took 6,292 s, section 23.1; base -38
took 4,498 s) are split into work units by `--unit-depth`. The library knows
the mean tree size per level (section 9.1) but not the spread. In a
branching-process view the subtree sizes have a law with a computable tail.
It gives the right unit depth for a given thread count and a time estimate
with an error bar before a run starts.

Attack: Read the per-unit node counts from existing journals, or rerun bases
28 to 34 with `--journal`. Fit the log node counts per unit. Compare with a
two-type branching model whose offspring law comes from the level counts of
`analysis/tree_model.py`. Measure the idle time at the end of each run.

Kind: computation.

### 79. Bottom-up information in bases with a small radical

In base `2^k`, an even digit `x >= k L` has `x^x == 0 (mod b^L)`. So the
bottom `L` digits of `S(c)` depend only on the counts of the odd digits and of
the even digits below `k L`. Can an exact search use this to prune from the
bottom in bases 32, 64 and 128?

Why: Section 10.4 concludes that "a large classical speedup would need a new
source of information about the low digits of `n`". In general bases there is
none (Proposition 10.2). In bases with a small radical there is some: the low
digits are a function of half the counts. This is the integer analog of the
Frobenius blocks of chapter 24, and the only exact low-digit information known.
A search that fixes the large counts from the top and the odd counts from the
bottom would test the bottom digits against the multiset early.

Attack: For `b = 32` and 64, count how many bottom digits of `S(c)` the odd
counts fix. In a toy Python search for base 32 with `d = 31`, compare the node
count of the plain tree with a tree that branches on the odd counts first and
checks the bottom digits. Report the ratio, not a speed.

Kind: computation.

## Theme XIII. Theorems about the model

### 80. Assumption R when `b - 1` is prime

Prove Assumption R of section 13.2.3 when `b - 1 = p` is prime, using bounds
for exponential sums of the self-power map, `sum over x < p of e(h x^x / p)`.

Why: This sharpens question 54. When `b - 1` has only small prime factors, the
digits run over many full periods of `x mod p (p - 1)`, and the distribution of
`x^x - x mod p` is explicit (Lemma 20.7). The hard case is a prime `p` close to
`b`. There the digits see each residue of `x` once, and the needed statement
is that `x^x - x mod p` does not concentrate, for `x < p`. The unconditioned
version reduces to
`min over h != 0 of (1/b) sum over x < b of (1 - cos(2 pi h (x^x - x) / p)) >= c > 0`.
Lead (computed, every odd prime power `q` dividing `b - 1`, `b <= 20,000`):
the minimum is at least 0.23. The worst cases are the powers of 3 at
`h = q/3`, where the rate tends to `1/4`, as Lemma 15.12 predicts (only
`x == 2 (mod 6)` moves the residue mod 3). For primes `p >= 101` dividing
`b - 1`, `b <= 6,000`, it is at least 0.757, and the worst cases are
`b - 1` prime. A uniform law would give 1. So in the Poisson model the
residue law is within `exp(-0.23 b)` of uniform in this whole range.

Attack: Compute this minimum for every odd prime power `q` dividing `b - 1`,
`b <= 20,000`, with an FFT of the histogram of `x^x - x mod q`. Search the
literature of direction A1 for a bound of the form `o(p)` on the sums. Then
handle the conditioning on the length event `G_d` of Lemma 13.10, which depends
only on the largest digits.

Kind: proof.

### 81. The length shares as a theorem in the model

Prove that in the basic model of chapter 5 the expected number of solutions
with `b - j` digits tends to the shares of section 5.2 (8.0%, 55.2%, 23.2%,
...) as `b` grows.

Why: Section 13.2.6 lists this as open: the limits are a Poisson computation,
not a theorem. Every later chapter that compares counts with "about one per
base" uses them. The proof is a statement about random strings only, so it
should be within reach.

Attack: Couple the digit counts of a random string of `b - j` digits with
independent Poisson variables (total variation `O(1/b)`). Show that the event
"`F` has `b - j` digits" depends, up to probability `o(1)`, only on the counts
of the digits above `b - C ln b`. Compute the limit from the weights
`(b - y)^(b - y) = e^(-y) b^(b-y) (1 + O(y^2 / b))`.

Kind: proof.

### 82. Is `k(B)` always the number of factors of `B - 1`?

In `F_q[T]`, Theorem 21.6 proves `k(B) >= omega(B - 1)`, and the census finds
equality in all 4,426 bases. Is it always an equality, for squarefree and for
non-squarefree `B - 1`?

Why: The free residue factor `q^k(B)` is the `F_q[T]` form of the parity
doubling, and section 21.1.8 rests the analogy on it. Section 24.4.5 adds a
second dimension, `kappa(B)`, which exceeds `k(B)` for some factor types. An
exact formula for `k(B)` closes the algebraic side of chapter 21.

Attack: The map is `D -> sum over j of (Phi^j(D_j) - D_j) mod (B - 1)`. Write
it on each primary factor `P^a` of `B - 1` with the Frobenius of
`F_q[T]/(P^a)`, and compute the codimension of its image. Check against the
census, then against `(q, e) = (2, 7)` and `(3, 5)` in
`analysis/data/r4f_census_*`.

Kind: proof.

### 83. A model that keeps the Frobenius blocks

Build the model that section 24.7 asks for: keep Corollary 24.3 exactly, so
that `F(x)` is assembled from `p_0, ..., p_(e-1)`, and treat as random only the
values that are not fixed by the blocks. Does it predict the census of Table
24.3.1 per type of `B - 1`?

Why: Heuristic 24.14 explains the `0^0 = 0` excess by forced lower classes
and the larger kernel `kappa(B)`, but it is not a model with numbers, and it
leaves the irreducible quartic of `(5, 4)` (ratio 2.0) unexplained. A model
that is exact on the blocks and random elsewhere is the `F_q[T]` version of the
forced-top-digit correction for the integers (section 23.5). It would show
whether "keep the forced digits, randomize the rest" is enough in a world where
the forcing is strong.

Attack: In `analysis/r4f_lib.py`, sample `x` and compute `F(x)` from the
blocks. Replace each `p_j` by a uniform digit of the same degree and keep the
block maps. Compare per type with Table 24.4.7 for `(q, e) = (5, 3)`,
`(7, 3)` and `(5, 4)`.

Kind: computation.

### 84. Open lengths in the factorial system

Section 21.5.3 finds that coincidences in the factorial system are "all or
nothing per length": a length `L` is open when the few values of the top
digits of `F` can place the largest digit in a top position. For which `L` up
to 100 is a length open, and what does a model that counts only open lengths
predict beyond `34!`?

Why: The plain model expects 4.5 solutions below `34!` and there are none
(P = 0.011 per convention). The near-solutions sit in 5 of 17 lengths. A model
with forced top digits would decide whether the set of solutions is finite
in this world, which is the open part of question 62.

Attack: For each `L`, enumerate the counts of the 3 or 4 largest digit values
that can occur, and compute the top digits of `F` from them, as the search of
`r3t_factorial.rs` does at its first levels. Mark `L` open if some branch is
consistent. Calibrate the rate per open length on `L <= 33`. Extend the census
to `L = 40` with 256-bit integers if the model predicts a solution there.

Kind: computation.

## Theme XIV. The model in more places

### 85. The image and in-degrees of `F`

For bases 10 to 16, what share of the digit multisets is in the image of
`c -> multiset of S(c)`, and what is the law of the in-degree? Does the
class-lumped random mapping of section 15.1.5 predict them?

Why: Cycles test the model on a handful of events per base (chapter 15). The
image share and the in-degrees test it on all `C(2b, b)` multisets, and they
include short multisets, where the per-base model was never checked. A
random mapping with classes of sizes `N_K` predicts an image share of
`sum over K of N_K (1 - exp(-m_K / N_K))` divided by the total, with `m_K` the
number of multisets mapped into class `K`.

Attack: Add an image bit and an in-degree counter to `dyn_cycles.rs`. It
already visits each multiset once. Run bases 10 to 16 under `0^0 = 1` (base 16
took 165 s for the cycle pass). Compare per class with the formula.

Kind: computation.

### 86. A mixing statistic for every world

For each world of chapters 14, 17 and 21, measure how much the digit histogram
of `F(c)` depends on `c` beyond the forced top digits. Does the model error
follow this statistic?

Why: Direction A4. The library has two failing worlds (factorial and
`F_q[T]`) and many working ones, and a different explanation for each
failure. One statistic that separates them would predict the model's error in
a new world before its census.

Attack: For random `c` of the dominant length, compute the histogram of the
digits of `F(c)` below the top 3 positions and the chi-square of its agreement
with `c` against a uniform string of the same length. Do this for the
integers at `b = 20`, base -20, factorions at `b = 20`, the factorial system
at `L = 12`, `F_q[T]` with `(5, 3)` and the Pisot base `x = 6`. Plot the ratio
of the two agreement rates against the model ratio of each world.

Kind: twist.

### 87. Narcissistic numbers in even bases 15 to 20

Section 19.4 finds that narcissistic numbers with `d >= 6` exceed the refined
model by 18% in even bases, mostly in bases 8 and 10, while odd bases and the
forced cells fit. Do bases 16, 18 and 20 show the same excess?

Why: This is the one place where the refined model, with no fitted parameter,
is off on data nobody tuned (P = 0.005). If the excess persists in fresh even
bases, the model misses an even-base effect for the weights `x^d`. That effect
would then be a candidate for the even-base deviations seen for `x^x`
(section 9.7).

Attack: Run `fast search --power d --zero 0 --min-digits d --max-digits d`
for bases 15 to 20 and the lengths where the model expects at least 0.01,
timing one length first. Use `r3c_narcissistic.py model` for the predictions.
Compare with the OEIS lists where they exist.

Kind: computation.

### 88. Chains with many self-paying digits under `0^0 = 1`

Theorem 15.14 gives solutions under `0^0 = 1` from a chain of digits that pay
for each other, and any set of self-paying digits below the chain top can join
it. Is there a base `r^t` where a chain top lands within the number of
available self-paying digits of the needed zero count, so that `N_1(b) >= 3`?

Why: Whether `N_1(b)` is bounded is open (section 8.4). Section 15.5 searched
`r <= 40`, `t <= 300` and found only base 64. The mechanism needs the chain top
to come within about `log2 b` of `r^(u_0)` plus the number of digits. Highly
composite `t` gives many self-paying digits (Proposition 2.2), which widens
the target.

Attack: Extend `analysis/dyn_power_digits.py` to `r` in {2, 3, 5, 6} and `t`
up to `10^4`, restricted to `t` with many divisors. Compute only the chain
positions and their distance to the target, without writing the numbers out.
Check any hit with exact integers.

Kind: computation.

### 89. A prefix test for the Gaussian base `-4+i`

Section 14.5 stops base -4+i at 22 digits, because a prefix of digits defines
a translate of a fractal tile, not an interval. Can a search use a convex hull
or a disk around each tile as its prefix test?

Why: The model puts 83% of the expectation of -4+i at 34 digits, so the census
of the Gaussian family stops one base short. A tile-based tree would also make
the Eisenstein base -4+w (section 21.3) and lengths 27 and 28 of -3+w
reachable, which completes three open ends of chapters 14 and 21.

Attack: Precompute a disk that contains the tile of `-4+i` with digits 0 to
16. In `gauss.rs`, decide counts from the largest digit down and prune a node
when the disk around the range of `F` misses the set of prefixes consistent
with the counts. Check against the enumeration up to 22 digits, then measure
the node count at 26 digits.

Kind: twist.

## Proposed workloads

Three workloads of five questions each, ranked by expected payoff.

Workload 1: near-solutions as evidence (Python, `fast`, existing data).

1. Question 73. The swap lemma is a one-line proof, and the lead shows that it
   matters. Every "chance" verdict of the library uses offset calibrations.
2. Question 72. Needs the corrected variance of question 73, then decides
   whether `D = 0` is special anywhere.
3. Question 74. The largest positive deviation, with a concrete mechanism to
   check.
4. Question 85. A cheap test of the model on all multisets of a base.
5. Question 86. Turns the per-world verdicts into one statistic.

Why this grouping: all five ask whether the library's calibration tool is
sound, and the first two share their data runs.

Workload 2: limits of search (Python, Rust, integer programming).

1. Question 77. A direct measurement of a method that Theorem 10.1 does not
   cover. A few hours, with a clear answer either way.
2. Question 75. Extends the only quantitative barrier to every order.
3. Question 79. The one known source of exact low-digit information.
4. Question 78. A constant-factor gain for long runs and honest time estimates.
5. Question 76. The hardest and the most valuable: a reason why no oracle
   method beats the tree.

Why this grouping: each question either finds a method outside the top-down
tree or narrows the reasons why none exists.

Workload 3: theorems about the model (PARI/GP, Sage, Python).

1. Question 81. A model theorem that every chapter cites, likely provable.
2. Question 82. A finite algebra problem with a census to check against.
3. Question 80. Sharpens question 54 to the hard case, with the self-power map
   literature as the tool.
4. Question 83. Tests "keep the forced digits, randomize the rest" where the
   forcing is strongest.
5. Question 84. Decides the open part of question 62 in model terms.

Why this grouping: all five replace a model computation or a census
observation by a proof or by a model with the right structure.

Left for later: questions 87, 88 and 89.
