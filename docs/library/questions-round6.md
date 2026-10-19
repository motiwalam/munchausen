# Round 6: directions and questions

A reading of the whole library, chapters 1 to 28 and the questions 1 to 89,
produced this file. Part A names seven directions. Each asks what the main
results really rest on, or which silent assumption could be dropped. Part B
poses 21 concrete questions, numbered 90 to 110, each raised by a result of
a named chapter. "Proposed workloads" groups 20 of them into four agent
workloads. "Problems found" lists errors and gaps that I noticed while
reading.

The leads come from quick runs by the questioner. The scripts are
`analysis/r6p_*.py`, and each prints the numbers quoted here. The numbers
are leads, not results.

## Part A. Directions

### A1. The expected count is a trace

The basic model of chapter 5 gives base `b` the expected count
`sum over d of P(F of a random d-digit string has d digits)`. Each term is
a diagonal entry of the length-transition matrix `M`: row `d`, column `d'`,
entry the chance that `F` of a random `d`-digit string has `d'` digits. `M`
is stochastic, because `F` never has more than `b` digits
(Proposition 15.1). So the expected count is `tr M`, which is 1 plus the
eigenvalues other than 1. If the length of `F` did not depend on the length
of the string, the rows near `d = b` would be equal and the trace would be
exactly 1. That is the reason behind "about one solution per base", which
section 14.6.3 states in words. The excess at a finite base is the sum of the
other eigenvalues. A quick computation puts the second eigenvalue near
`3 / b` (question 90).

Add the residue modulo `b - 1` to the classes and the refined model is the
trace of the larger matrix. An invariant residue splits that matrix into
blocks, and each block brings one more eigenvalue 1. The parity doubling
(section 5.3), the factor `b - 1` of forced residues (section 17.2) and the
factor `q^k(B)` of `F_q[T]` (Theorem 21.6) are multiplicities of the
eigenvalue 1. The factor `1 + e^-2` is 1 plus the eigenvalue `e^-2`.
Chapter 15 already counts cycles of length `L` by `tr(M^L) / L`. So chapters
5, 13, 15, 17 and 21 state one fact: the arithmetic of `x^x` enters the
model only through this spectrum. This has a sharp consequence. Once the
residues are in, any further deviation must come from a structure that the
class matrix cannot see. The library has found two such structures: the
forced top digits (sections 11.2, 23.5) and the identities that make the
families of chapters 2, 22 and 25. It has never found a third. The 12% excess
under `0^0 = 1` (section 23.5, z = 3.0 after chapter 26) is either the first
example of a third kind or a flaw in the model. Question 93 is the cheapest
way to decide.

### A2. Local and global corrections: one heuristic for every length

Short solutions follow the root heuristic of section 11.4: a spacing term
`1 / Q_s'(b*)` times local factors at small primes. Long solutions follow the
per-base model: a length term times the residue factor modulo `b - 1`, with
a correction for the forced top digits. Both have the shape of a
Hardy-Littlewood heuristic, a singular integral times a singular series. I
think they are one heuristic. The local factor at `q` for a multiset `c` in
base `b` is the share of its arrangements whose value is `== S(c) (mod q)`,
compared with `1/q`. For `q | b - 1` all arrangements agree, which is the
digit-sum identity. For `q` prime to `b (b - 1)`, a long multiset has many
arrangements that spread over the residues, and the factor is 1. A short
string has few arrangements, and the factor is far from 1. That would
explain why short solutions run 2 to 4 times above the per-base model in
every world (sections 10.5, 14.6.2, 17.4, 19.4). It would also say at which
length to switch from one heuristic to the other (questions 91, 92).

The same split works for obstructions. The covering theorems (15.13, 20.13)
are p-adic: no root modulo `27` or `81`. The square-class results
(Theorem 8.3, Theorem 25.7 (ii)) are real, or Archimedean: the root sits
within `1/(2x)` of an integer and never reaches it. Is every family of
strings with one free digit that is never a solution excluded by one of
these two kinds, as in a Hasse principle? The families of chapter 22 are the exceptions that pass
both tests, and they are identities.

### A3. The digit zero

Many loose ends pass through the digit 0. It carries the convention. It
makes the twins. It is the parity channel under `0^0 = 1` in odd bases
(section 5.3), and in `F_q[T]` the whole `0^0 = 1` gap of the model is the
zero count (Proposition 24.11). The long solutions under `0^0 = 0` have too
few zeros (section 24.6.2, question 71), the zero-free solutions are 24
against 16.5 expected (section 17.3), and the near-solution rate under
`0^0 = 1` is 12% too high. A new lead: in even bases, where the model gives
both conventions the same expectation, the near-solutions with zeros are
about 23% more common under `0^0 = 1` (question 93). A world without the
digit 0 exists: bijective numeration, with digits 1 to `b`. It has no
convention, and the digit `b` pays for itself at position `b - 1` in every
base (question 95). The direction is to split every count of the library by
the number of zeros, and to see which anomalies survive.

### A4. Why some weights have identity families

Corollary 22.7 refuted the finiteness conjecture of chapter 3 because `x^x`
is a `j`-th power for every `x == 0 (mod j)`. The condition on the large
digit is a congruence, which a whole progression satisfies. For factorials
the opposite holds. By Bertrand's postulate a prime in `(x/2, x]` divides
`x!` exactly once, so for large `x` the number `x!` is never a bounded
multiple of a perfect power.
Also `x! == 0` modulo every prime up to `x`. So the local test that cannot
work for `x^x` (Proposition 16.8) should work for factorions. Short
factorions with one large digit should be finite: unconditionally for three
digits apart from one case of Brocard type, and under GRH for every length
(questions 97, 98). Lead: the 3-digit factorions in all bases up to
`10^131` are 7, and the largest, `(2,4,10)` in base 1346, is the identity
`10!/2 + 9 = 1347^2`, an equation of the Brocard-Ramanujan kind. So the
factorion world shows where "short solutions are finite" can become a
theorem, and where a famous open problem takes over. The `x^x` world has
neither escape: no vanishing residues and no lack of families. That
calibrates how hard the open questions of chapters 8 and 25 are.

### A5. Existence

The library proves non-existence, upper bounds and identity families. No
theorem says that coincidences happen. Nothing proves that a positive share
of bases has a solution, or even that every large base has an `n` with
`|n - F(n)|` well below `n`. The model makes both statements obvious. Which
existence statements can be proven? Three candidates: near-solutions in
every base with a few top digits matched (question 100), averages over the
base, which may also push Theorem 20.3 past its barrier at
`ln b / ln ln b` (question 101), and long structured solutions under
`0^0 = 1` (question 99).

### A6. The evidence as a whole

The library has run about a hundred tests of the model and judged each one
alone, with corrections for selection made by hand ("about 16 groups").
With that many tests a few P values near 0.01 are expected. What survives
after chapter 26: the odd-base factorions (P about 0.13 after selection), the
5-digit excess (about 0.018), the 12% excess under `0^0 = 1` (z = 3.0) and
the class modulo `2x` of the even Pisot bases (not chance). Two things would
change beliefs more than another analysis of old data. One is a ledger of
all P values, to see whether they lean in one direction (question 103). The
other is fresh data with predictions written down before the run. Bases 42
to 46 now take about 16 hours with `--hybrid` (question 104).

### A7. What is left for the search

Theorem 27.5 says that every method that learns through intervals needs
about the exact tree, and Theorem 27.2 says that every tree that reveals
counts needs about `1.638^b` nodes. Section 27.4 says that bottom digits cost
more than they prune. The remaining room is the middle digits of `S`, about
which nothing is known (question 109), constant factors, and quantum search.
So the search helps most now as a source of fresh data, and one target
stands out: the first `b`-digit solution under `0^0 = 1`, which would refute
the conjecture that started the project (question 105).

### Which directions help the exact search

A6 and A7 use the search; A7 decides whether a faster exact method is still
worth looking for. A1 to A5 improve the theory and the predictions. A2
would also say at which lengths the `kdigit` sieve and the tree should hand
over (question 29).

## Part B. Questions

## Theme XV. One formula for the expected count

### 90. The expected count is the trace of a stochastic matrix

Let `M_b` have the entries `P(F of a uniform d-digit string has d' digits)`
for `d, d'` from 1 to `b`. Prove that the basic model's expected count is
`tr M_b`, that the rows with `d = b - j`, `j` fixed, converge to one law
(the length shares of section 5.2), and that `tr M_b = 1 + c / b + O(1/b^2)`.
What is `c`? Then prove the same for the refined model with the classes
(length, residue modulo `b - 1`).

Why: One matrix carries the "one per base" law (section 14.6.3), the length
shares (question 81), the parity doubling (5.3), the factor of forced
residues (17.2), `q^k(B)` (21.6), `1 + e^-2` and the cycle counts
`tr(M^L) / L` (Proposition 15.6). Question 81 becomes the statement that the
law of the length of `F` does not depend on `j`. The excess at finite bases,
1.25 per convention at base -10, 1.10 at base 20 and 1.04 at base 40
(sections 14.3.1 and 13.2.5), becomes the sum of the other eigenvalues. Lead
(computed, `r6p_trace.py`, basic model, `0^0 = 1`, 20,000 strings per
length, lengths 1 to `b`): `tr M - 1` is 0.55, 0.28, 0.125 and 0.047 at
`b` = 10, 20, 40 and 100. The second eigenvalue is 0.31, 0.13, 0.081 and
0.030, about `3 / b`. The product `b (tr M - 1)` is 5.5, 5.6, 5.0 and 4.7.

Attack: Write the length of `F` as a function of the largest digit present
and its count, as section 5.2 does. Changing `d` by one moves the Poisson
means by `1/b`, so neighbouring rows differ by `O(1/b)`, and a perturbation
bound gives the trace. For the refined model, show that the class matrix is
block diagonal exactly in the case of Theorem 15.2. Show that its other
eigenvalues are the character sums of section 13.2, as computed in the lead
of question 80.

Kind: proof and computation.

### 91. Arrangements and the local factor

For a digit multiset `c` of length `k` in base `b`, and a prime power `q`
prime to `b (b - 1)`, what share of the arrangements of `c` have a value
`== S(c) (mod q)`? Prove that it is `1/q` up to an error that is
exponentially small in `k / ord_q(b)`. Find the length below which it is
not.

Why: Short solutions exceed the per-base model by a factor 2 to 4 in every
world (sections 10.5, 14.6.2, 17.4, 19.4). The root heuristic explains this
with local factors (sections 11.4 and 19.3). The per-base model has no local
factor apart from `b - 1`. Both are right if the arrangements of a long
multiset spread over the residues and those of a short one do not. A proof
would make the two heuristics one (direction A2) and give the crossover
length that sections 22.4 and question 29 approach by calibration.

Attack: Modulo `q`, the value `n = sum s_i b^i` depends only on the digit
sums over the `ord_q(b)` classes of positions. For a random arrangement
these sums are multivariate hypergeometric. Bound `E e(h n / q)` by a
product over the classes, as in a local limit theorem. Then compute the exact
share for `k` = 3 to 12, `q` = 3, 4, 5, 7, 8, 9 and bases 9 to 30, and
compare it with the factors `rho_s(q)` of `analysis/root_local.py`.

Kind: proof and computation.

### 92. The two heuristics at medium lengths

For lengths 6 to 12 in bases 7 to 20, do the root heuristic with p-adic
factors (section 19.3) and the refined per-base model with forced top digits
(section 23.5) predict the same number of solutions? Which one matches the
window calibration of section 22.4 and the census of `output/`?

Why: Section 22.4.4 fits the 6-, 7- and 8-digit counts of bases 3 to 12 with
the window calibration. The per-base model is calibrated only for lengths
`b - 6` to `b`. Every length in between appears in the census of bases 9 to
20. If the two heuristics agree there, direction A2 is right. If not, the gap
measures a missing factor, perhaps the one behind the 5-digit excess
(section 22.4.3).

Attack: Run `analysis/r3c_root_spectrum.py` for `k` = 6 to 12 with digits up
to 20. Extend `analysis/r2c_top_model.py` to all lengths. Use
`analysis/r4b_spectrum.c` for the window estimate of the same cells. Compare
cell by cell with the counts of `output/b2-41-*.txt`.

Kind: computation.

## Theme XVI. The digit zero

### 93. Where the 12% excess under `0^0 = 1` sits

The near-solution rate under `0^0 = 1` is 12% above the refined model in
both parities (section 23.5; z = 3.0 with the variance of chapter 26), while
`0^0 = 0` fits (0.98). Does the excess sit in the near-solutions with zeros,
and do perturbed worlds show it?

Why: This is the largest deviation from the model on the true weights that
chapter 26 left standing. In even bases the refined model gives both
conventions the same expectation, and a near-solution without zeros counts
under both. So in even bases any difference between the conventions sits in
the near-solutions with zeros. Lead (computed, `r6p_zeros.py conv`, the
strings of `analysis/data/r5e_int_std.txt`: bases 12 to 26, offsets
`2j(b-1)` with `j = 1..60`, at least `b - 6` digits): even bases have 177
distinct multisets with zeros among their near-solutions under `0^0 = 0` and
217 under `0^0 = 1`, and 127 zero-free ones under both. The surplus has one
or two zeros: 176 and 67 strings under `0^0 = 0`, 248 and 90 under
`0^0 = 1`. Strings with three or more zeros go the other way, 26 against 12.
With clusters the difference is about 2 standard deviations. If perturbed
weights show the same gap between the conventions, the cause is the model's
treatment of zeros or the offsets. If they do not, it is arithmetic of
`x^x`, the third kind of correction of direction A1.

Attack: (1) Rerun `analysis/r5e_int_offsets.py` with `--perturb` seeds 1 to
5 in bases 12 to 26, both conventions, strings kept, and compare the counts
with zeros. (2) Split the refined model by the number of zeros
(`analysis/wgt_model.py`) and compare zero class by zero class. (3) Since
`F_1 = F_0 + c_0`, a near-solution under `0^0 = 1` with `c_0` zeros at offset
`D` is a near-solution under `0^0 = 0` at offset `D + c_0`. Count the
offsets `2j(b-1) + c` with `c` = 1 and 2 under `0^0 = 0`, restricted to `c`
zeros, and see which offsets carry the surplus.

Kind: computation.

### 94. Do near-solutions share the zero deficit of question 71?

The long solutions under `0^0 = 0` in bases 12 to 41 have 29 zeros against
42.5 expected (section 24.6.2). Do the near-solutions show the same deficit
once the forced top digits are in the model?

Why: Question 71 rests on 48 solutions, and near-solutions give thousands of
digits. If they show no deficit, question 71 is chance. If they do, the
zeros of `F` follow another law below the top digits, against Table 24.6.1.
Lead (computed, `r6p_zeros.py`): counted once per distinct multiset, the
near-solutions under `0^0 = 0` have 262 zeros against 258 from a binomial
law in even bases, and 444 against 504 in odd bases. The forced top digits
are rarely 0, which lowers the binomial expectation by about 10%, enough to
absorb the odd-base gap. Counted per string, the zero rate times `b` in the
middle positions is 0.99 in even bases and 0.69 in odd bases, but a few
large clusters dominate that number. So the lead leans toward chance for
question 71.

Attack: Compute the expected number of zeros per multiset in the
second-order model of `analysis/r2c_top_model.py` (top 3 digits forced).
Compare it per multiset with the near-solutions, using the clustered
variance of chapter 26. Do the same for the solutions of bases 12 to 43.

Kind: computation.

### 95. Bijective numeration: no zero, and a self-paying digit in every base

In bijective base `b`, the digits are 1 to `b` and every positive integer has
exactly one representation `n = sum s_i b^i`. There is no `0^0`. The digit
`b` at position `b - 1` pays for itself, since `b * b^(b-1) = b^b`. So every
`(b-1)`-digit solution `m` gives the `b`-digit solution `(b, m)`. How many
solutions does a base have, and does the model, with this identity built in,
predict them?

Why: The digit 0 carries the convention and several anomalies (direction
A3). This world removes it and keeps the rest: `n == digit sum (mod b-1)`
still holds, and `x^x == x (mod 2)` makes odd bases double with no penalty
for zeros. It also has what the integers have only in perfect powers: a
self-paying digit in every base, which pairs the most common length `b - 1`
with the length `b`. Lead (computed, `r6p_bijective.py`, brute force over
multisets): bases 2 to 10 have 1, 4, 4, 1, 4, 1, 0, 3 and 2 solutions with
at least 2 digits. The pairs `(b, m)` occur in bases 2, 3, 4 and 6, for
example `(2,2,3,5,2)` and `(6,2,2,3,5,2)` in base 6. A zero-free integer
solution without the digit `b` is also a bijective solution, such as 3435 in
base 10. Base 10 also has an 11-digit one, `(1,10,4,3,8,5,7,8,10,8,9)`.

Attack: Prove the length bound and the invariant residues with question 108.
Adapt `fast`: the numbers with a fixed top part still form an interval, so
the prefix test carries over. Run bases 2 to 30, build the model with the
bijective length windows and the residue modulo `b - 1`, and add the pairing
exactly.

Kind: twist (proof and computation).

## Theme XVII. Why some weights have families

### 96. A criterion for identity families

For which weights `w` does every length `k >= 3` have infinitely many
solutions? Conjecture: exactly when, for some `j >= 2` and some `lam`, the
set of `x` with `w(x)` in `lam` times the `j`-th powers contains an
arithmetic progression that is compatible with the constructions of
Theorems 22.6 and 25.5.

Why: The families of chapters 22 and 25 exist because `x^x` is a `j`-th power
on the progression `x == 0 (mod j)`. The weights `x^(x+t)` have the same
property, on `x == -t (mod j)`. Factorials have none, by Bertrand's
postulate. The weights `x^d` give only the thin set of perfect powers. A
criterion says in advance which worlds have finite lists of short solutions,
and therefore where finiteness can be proven (questions 97 and 98).

Attack: Rerun the census of section 25.1.5 (`analysis/r5f_identities.py`)
with the weights `x^(x+1)`, `x!` and `x^d`. Theorem 25.2 needs only
`w(d) >= d`, so it holds for all of them. Prove the "no family" half for
`x!` from Theorem 25.4 and Bertrand's postulate.

Kind: proof and computation.

### 97. Three-digit factorions are finite, except for a Brocard case

Prove that for each pair of small digits, the 3-digit factorions whose third
digit `x` is large are finitely many, with an explicit bound, when `x` is the
last or the middle digit. Reduce the case of `x` in front to equations of
the form `4 x x! + s^2 = U^2`.

Why: In the `x^x` world no finite set of congruences can bound the free digit
(Proposition 16.8), because `x^x mod l` is periodic in `x`. For factorials,
`x! == 0 (mod l)` for every prime `l <= x`. Completing the square as in
Theorem 25.7 gives `(2 p b + q)^2 = 4 p x! + K(x)`, so `K(x)` must be a
square modulo every prime up to `x` that does not divide it. `K(x)` is a
polynomial of degree at most 2 in `x`. If it is not a perfect square, a bound
for the least quadratic non-residue gives a prime `l <= x` where this fails.
This is the argument by which Dabrowski (1996, as I remember it; the
reference must be checked) proved that `x! + A = y^2` has finitely many
solutions for every `A` that is not a square. When `x` is last,
`K(x) = 4p (p! + q! - x) + q^2` is negative once `x` is large. When `x` is in
the middle, `K(x) = x^2 + 4p (p! + r! - r)` is a square for only finitely
many `x`. Only a leading `x` leaves infinitely many square values of `K`, and
then the equation asks for two divisors of `4 x x!` that are very close,
like Brocard's `n! + 1 = m^2`: open, and finite under abc (Overholt). Lead
(computed, `r6p_factorion3.py`, digits up to 150, so complete for every base
up to `10^131`): with `0! = 1` the 3-digit factorions are `(1,4,4)` in
base 5, `(1,4,5)` in base 10, `(6,6,1)` and `(6,6,2)` in base 15, `(7,2,5)`
in base 27, `(1,6,6)` in base 35 and `(2,4,10)` in base 1346. The last one
is `10!/2 + 9 = 1347^2`, a Brocard-Ramanujan equation, and its `K(10) = 144`
is a square. A proof would be the library's first unconditional finiteness
theorem for a family of short strings with a free digit, in any world, and
it would show exactly where a famous open problem takes over.

Attack: Take the three positions of `x` as in Theorem 25.7. Show that `K(x)`
is not a square beyond an explicit bound. Use a Burgess-type bound for the
least prime `l` with `(K(x) / l) = -1`, which is far below `x` since
`|K(x)|` is about `x^2`, and avoid the primes that divide `K(x)`. Check the
small `x` with `r6p_factorion3.py`. For two large digits, both factorials
vanish modulo the primes below the smaller one; find how far the argument
reaches.

Kind: proof.

### 98. Factorions of every length under GRH

Assume GRH. For a fixed prefix of `k - 1` digits, are the `k`-digit
factorions with a large last digit `x` finitely many, with a bound
polynomial in the prefix? Is the set of `k`-digit factorions finite for every
`k`?

Why: The argument of question 97 needs only one prime `l <= x` at which the
reduced polynomial `A(r) + x - F(t)` has no root modulo `l`. Effective
Chebotarev bounds under GRH (Lagarias and Odlyzko; Bach and Sorenson) give
such a prime below a power of `log x`, as long as the polynomial has no
rational root, which happens for finitely many `x`. Factorions would then be
the first world of the library where every length provably (under GRH) has
finitely many solutions, against the `x^x` world, where every length has
infinitely many (Corollary 22.7).

Attack: Do the last digit first. Then a large digit in another position,
where `x` is a coefficient. Then several large digits, where the smallest one
bounds the usable primes. Check the bounds against a `kdigit` run with
factorial weights; the masks of section 11.5 work for any weights.

Kind: proof (conditional) and computation.

### 99. Long structured solutions under `0^0 = 1` (speculative)

Is there an infinite family of solutions under `0^0 = 1` whose length grows
at least like `log b`?

Why: Under `0^0 = 0`, base `n^(n-1)` has the self-paying solution
`(n^(n-2), 0, ..., 0)` with about `b ln ln b / ln b` digits (Theorem 9.2).
Under `0^0 = 1` the known infinite families have a fixed length and bases
that grow like towers (sections 22.3.2 and 25.1.2), and the longest
structured solution is the 11-digit chain of base 64 (section 15.5). Zeros
must be paid, and Theorem 15.14 pays them with the last digit. A family of
long structured solutions would change the length law (Conjecture 10.3) as
the binomial families changed chapter 3, and it could give large `N_1(b)`
(question 88 and section 7.4).

Attack: In Theorem 15.14 the number of zeros below the leading digit must be
`c - 1` with `c = r^(u_0)`. Search the bases `r^t` with `t` up to `10^5` and
many self-paying digits for chains whose top position falls within the reach
of the self-paying digits, as question 88 does, but rank them by length.
Then try two chains that share one last digit.

Kind: proof and computation.

## Theme XVIII. Existence and averages

### 100. Near-solutions that provably exist (speculative)

For which `t` can one prove that every large base has an `n >= b` with
`0 < |n - F(n)| < n / b^t`? Is `t = 2` within reach, or a `t` that grows with
`b`?

Why: The library has no existence theorem for coincidences in a given base;
it has only the identity families. The model puts many near-solutions with
`|D|` of size `b` in every base (section 11.1). Matching the leading digit of
`F` in `n` gives `|D| < n / p` with `p` about `b / e`, so `t` just below 1
should be easy. Each further matched digit adds 1 to `t`. A proof for a `t`
that grows with `b` would be the first unconditional statement that `F`
comes close to the identity in every base.

Attack: Fix the counts of the largest digits so that `S(c)` has a given
leading digit, add that digit to `c`, and show by monotonicity in the
counts that some choice is a fixed point. Repeat for the second digit. The
top digits of `sum m_y (b-y)^(b-y)` are the digits of a real number close to
`b^b sum m_y e^(-y) b^(-y)`, so each further digit needs control of the
base-`b` digits of such numbers. That is where the method may stop.

Kind: proof.

### 101. Beyond `ln b / ln ln b` by averaging over bases

Can one prove that almost all bases have no solution with at most
`alpha ln b / ln ln b` digits for some `alpha > 1`, by averaging over the
bases instead of counting candidates one at a time?

Why: Theorem 20.3 stops at `alpha = 1`, because the multisets then
outnumber the bases (section 20.1.5). The condition `b - 1 | F(c) - S(c)`
would cut the count by about `b` if the residues were spread out, and no
method proves that for one base. On average over the bases the structure is
simpler. Split the digits of `c` into large ones and small ones with
weights below `b / k`. The small part of `F(c) - S(c)` is then an integer
below `b`, so once the large digits and the base are fixed, the divisibility
fixes that integer up to two values. The count becomes a sum, over the large
parts and the bases in their windows, of `r(N)`, the number of multisets of
small digits whose weights minus digits add up to `N`. Bounds for such
representation numbers come from additive combinatorics.

Attack: Write the count in this form. Bound `r(N)` by the number of
partitions of `N` into parts `x^x - x`. Evaluate the bound at `B = 10^96` as
in section 20.1.3, and see whether it stays below `B` beyond `K = 49`.

Kind: proof.

### 102. The abc conjecture and the 3-digit list

Does the abc conjecture imply that all but finitely many 3-digit solutions
under `0^0 = 1` with one large digit are members of the families of
Theorem 25.7 (i)? What remains with two large digits?

Why: Proposition 16.9 and Theorem 15.10 use abc for one equation each.
Theorem 25.7 (iii) turns every 3-digit string with one large digit `x` into
`U^2 - N = R` with `N = 4 l x^x` and `|R| <= 9 x^2 B^B`. The radical of the
triple `(R, N, U^2)` is at most `|R| x U`, while `U^2` is about `x^x`, so abc
bounds `x` for each `B`. That would prove Conjecture 25.8 for 3 digits and
one large digit, conditionally. The true residue is then the range of two
large digits left open by Theorem 25.11. There the dominant term
`u^u + v^v` is not a perfect power, which is also the case `a^a ~ c^c` that
Theorem 15.10 leaves out for 2 digits.

Attack: Compute the abc quality as in Proposition 16.9 for each position of
`x`, and make the dependence on `B` explicit. For two large digits, write
`F = u^u (1 + v^v / u^u)` and check whether a Fermat-Catalan type statement
covers it.

Kind: proof (conditional).

## Theme XIX. Evidence and fresh data

### 103. A ledger of P values

Collect every P value and z-score that the library reports for a test of the
model, about a hundred in chapters 4 to 28, including the table of section
26.4. Once dependent and nested tests are merged, are the P values uniform,
or do they lean in one direction?

Why: The library judges each anomaly alone and corrects for selection by
hand. A ledger gives one answer for all of them. A lean toward small P values
for too few solutions at `D = 0` would point to a systematic flaw, such as a
bias of the offset calibration; section 26.5 found a common ratio of 0.91
outside the two named worlds. Uniformity would close most "chance" verdicts
at once.

Attack: Tabulate the test, its statistic, its P value, its data, and whether
the hypothesis was named before the data were seen. Group the tests that use
the same data and keep one per group. Compare the P values of hypotheses
named in advance with the others, with a QQ plot and a Fisher combination.

Kind: computation.

### 104. A pre-registered census of bases 42 to 46

Before running, commit the model's predictions for bases 42 to 46 under both
conventions: counts, empty bases, lengths, zeros, `b`-digit solutions, and
each base's near-solution rate. Then run the exact search with `--hybrid`.
Which anomalies of directions A3 and A6 survive?

Why: The exhaustive data stop at base 43; base 44 was searched only with
`--deficit 2 --band 2.5`. Each anomaly was found in data that also chose
it. Base 34 takes 13 s with `--hybrid` (Table 28.3.3). At 1.9 per base,
bases 42, 44, 45 and 46 take about 0.6, 2.3, 4.4 and 8.4 hours on the test
laptop, 16 hours in all; base 43 is already done. Each base expects about
1.1 to 2.1 solutions per convention, and the near-solutions add a few
hundred events. The run also settles whether base 44 is empty under
`0^0 = 0` (probability 0.85 by section 9.3).

Attack: Write the predictions with `analysis/model.py`,
`analysis/r2c_top_model.py` and `analysis/thy_poisson.py` and commit them.
Run `fast search 42 46 --hybrid`, split with `--shard` because `--journal`
does not work with the GPU. Count near-solutions at transposition-free
offsets (Definition 26.7).

Kind: computation.

### 105. The first `b`-digit solution under `0^0 = 1`

Is there a base `b <= 55` with a `b`-digit solution under `0^0 = 1`?

Why: The original conjecture of section 7.1 holds for bases 3 to 45. The
model expects a `b`-digit solution in about 8% of large bases, and less at
finite bases because of the forced top digits (a factor 0.86 to 0.91 near
base 30, section 11.2). A counterexample settles the conjecture that started
the project. A long run without one tests the forced-top correction where it
matters most. The `b`-digit numbers cost 11% to 17% of a z-score run
(section 28.2.1).

Attack: Run `fast search b --min-digits b --zscore 3.4 --zlaw cond --hybrid`
for `b` = 46 upward, timing each base before the next. The expectation is
about 0.06 per base, so bases 46 to 54 give about 0.5, for about a day and a
half of the test laptop. Check every hit with exact integers.

Kind: computation.

### 106. Are neighbouring bases independent?

Are the counts and the near-solution rates of bases `b` and `b + 1`
independent, as the second half of Conjecture 10.3 and the empty-base law
assume?

Why: The sums `S(c)` are the same numbers in every base; only their digits
change. A multiset with largest digit `X` is a candidate in base `X + 1`
with `J = 1`, in base `X + 2` with `J = 2`, and so on. Its top digits in
bases `b` and `b + 1` are related through the factor `(1 + 1/b)^(d-1)`,
about `e`. The second Borel-Cantelli lemma of section 10.5 needs
independence across bases, and so does the variance of every pooled count.

Attack: Correlate the residuals `lambda(b) / model` of sections 23.5 and
26.4 for neighbouring bases 12 to 32. Count the multisets that are
near-solutions in two neighbouring bases at once
(`analysis/data/r5e_int_std.txt` has the strings). In the model, compute the
joint law of the top three digits of `S` in bases `b` and `b + 1`.

Kind: computation.

## Theme XX. Other worlds

### 107. The class modulo `2x` in even Pisot bases

In even Pisot bases under `0^0 = 0`, the offsets `j x` with even `j` carry 1.4
to 2.4 times as many near-solutions as those with odd `j` (section 26.6.2).
Why? Is the parity of `A_2 + A_3` biased for the greedy expansions of the
integers of one length?

Why: This is the one structure of chapter 26 that is not chance, and its
cause is open. Section 26.6.2 proves `(N - sum d_i) / x == A_2 + A_3 (mod 2)`.
So `N == F (mod 2x)` holds exactly when `A_2 + A_3 == (F - sum d_i) / x
(mod 2)`. If the greedy expansions of the integers in a length window favour
one parity of `A_2 + A_3`, and the weights favour one parity of
`(F - sum d_i) / x`, the class factor follows, like the parity doubling of
section 5.3. Lead (computed, `r6p_zeros.py peak`): the integer bases show
nothing of the kind. In bases 12 to 26 the near-solutions per offset are
flat in `j` from 2 to 120: 23.2 to 25.2 under `0^0 = 0` and 18.3 to 21.6
under `0^0 = 1`, in bands of ten offsets. So the effect belongs to the Pisot
expansions.

Attack: For `x` = 2, 4, 6 and 8 and every `N` up to `10^6`, tabulate
`A_2 + A_3 (mod 2)` by length `T`. Tabulate `(F - sum d_i) / x (mod 2)` for
the multisets that meet the identity modulo `x`. Predict the class factor
from the two tables and compare it with section 26.6.2.

Kind: proof and computation.

### 108. One invariant-residue proposition for every positional system

In a positional system with place values `beta_i` (integers, or algebraic
integers as in the Gaussian and Pisot bases), prove that the digit multiset
determines `n` modulo an ideal `I` exactly when `I` contains every difference
`beta_i - beta_j` of two positions that can exchange their digits. The
identity modulus, the parity factor and the offset class of the swap lemma
all come from this ideal.

Why: Propositions 10.2, 14.4, 14.9, 21.5, 21.12, 21.14 and Lemma 26.4 prove
this fact seven times, world by world. One statement predicts the identity
modulus of a new world before its census: `b - 1` in bijective base `b`
(question 95), and the moduli of balanced ternary or of the base `-3/2`. In
the Pisot base the rule "a digit `x` is followed by 0" restricts the
exchanges, so the ideal may be smaller than `(x)` on some lengths, which is
a candidate for question 107.

Attack: Write the proof once, with the admissibility rules of each system as
a graph of allowed exchanges. Apply it to the Pisot base and check whether
the restricted exchanges give the class modulo `2x`.

Kind: proof.

### 109. Is anything about the middle digits cheap? (speculative)

Is there a function of the digit counts, computable in time polynomial in
`b`, that predicts a digit of `S(c)` below the forced top digits and above
the bottom digits better than chance?

Why: Every method that learns through intervals needs about the exact tree
(Theorem 27.5), and the bottom digits cost more than they prune (section
27.4). A faster exact search would have to read middle digits. If no cheap
predictor exists, the oracle model is the right model of the real problem,
and the search question is closed up to constant factors and quantum
methods. If one exists, it is the new information that section 10.4 asks
for.

Attack: For bases 20 to 40, sample count vectors and fit simple predictors
for the digit of `S` at positions `d/3` and `d/2`: linear functions of the
counts modulo `b^j`, and nearest neighbours on the large counts. Measure the
information they carry against random digits. A rigorous version: prove that
the middle digits of `S` are equidistributed given the large counts, in the
Poisson model of chapter 13.

Kind: computation.

### 110. A last-digit factor in negative bases?

In negative bases the offsets that keep `n - F(n)` modulo `b` carry fewer
near-solutions than the others: 19.15 against 24.90 under `0^0 = 0` in the
bases that are not multiples of 3 (section 23.2), 2.9 standard deviations
after chapter 26. Is there a last-digit factor in base `-b`, and is it
missing in positive bases?

Why: Question 23.d of chapter 23 was never numbered. In positive bases the
last-digit factor `E[b c_v / d]`, with `v = S mod b`, is 1.00 within 0.01 in
bases 10 to 64 (lead of direction A5 of round 5). In base `-b` the last digit
of `n` is again `n mod b`, so the same factor should apply, and a value well
below 1 would be a real effect of the negative windows. A value of 1 makes
the 2.9 standard deviations chance.

Attack: Sample multisets of the dominant lengths of bases -10 to -27 (odd
lengths, `analysis/wld_negamodel.py`), compute `E[b c_v / d]`, and compare
with the ratio of the two offset families per base.

Kind: computation.

## Proposed workloads

Four workloads of five questions each, ranked by expected payoff.

Workload 1: is the refined model complete? (Python, existing data and
engines, a few hours.)

1. Question 93. The largest deviation from the model on the true weights,
   with a concrete lead and a cheap test in perturbed worlds.
2. Question 94. Uses the same data; closes or sharpens question 71.
3. Question 90. Turns the model's main laws into one statement about a
   spectrum, and makes question 81 a corollary.
4. Question 103. One global answer for all the "chance" verdicts.
5. Question 106. Checks the independence that the length window and the
   pooled variances assume.

Why this grouping: all five ask whether the refined model, with the forced
top digits, accounts for everything apart from identities. If question 93
finds a third kind of correction, the others say how large it is.

Workload 2: factorials against `x^x`. (PARI/GP, Python, one day.)

1. Question 97. Likely provable, and the library's first unconditional
   finiteness theorem for short strings with a free digit.
2. Question 98. The same argument for every length, under GRH.
3. Question 96. The criterion that explains why `x^x` has families and `x!`
   does not.
4. Question 102. What abc gives for the 3-digit list of `x^x`.
5. Question 99. The `0^0 = 1` side of the family question.

Why this grouping: the five questions turn the contrast between the weights
into theorems and show where famous open problems (Brocard, abc) block the
rest.

Workload 3: fresh data. (Rust and the GPU, about three days of the test
laptop.)

1. Question 104. Pre-registered exact census of bases 42, 44, 45 and 46.
2. Question 105. The first `b`-digit solution under `0^0 = 1`.
3. Question 95. A census of bijective bases 2 to 30, with a new engine.
4. Question 107. The Pisot class modulo `2x`, with a table of expansions.
5. Question 110. A cheap model computation for the negative bases.

Why this grouping: each question produces data that the existing
hypotheses did not see, and two of them can settle a conjecture.

Workload 4: one heuristic and existence. (Proofs, with small computations.)

1. Question 91. The arrangement factor, which joins chapters 5 and 11.
2. Question 92. The check of question 91 at medium lengths.
3. Question 108. One proposition for seven world-by-world proofs.
4. Question 101. A route past the barrier of Theorem 20.3.
5. Question 100. The first existence statement for near-solutions.

Why this grouping: the first three unify existing results, the last two try
statements in a direction the library has not touched.

Left for later: question 109.

## Problems found

1. Section 7.6 is out of date. It says that under `0^0 = 1` "every known
   infinite family relies on zeros that weigh nothing, or has 2 digits", and
   that the catalog of chapter 3 has no other structured example. Corollary
   22.7 and Theorem 25.5 give infinite families of every length under
   `0^0 = 1`, and section 15.5 gives the chain of base 64. The last bullet,
   "only the families of chapter 2 are known", is out of date too.
2. Chapter 25 keeps draft numbers. The summary cites "Propositions 3.4, 3.5"
   for Propositions 25.16 and 25.17, and "heuristic (2.4)" for
   Heuristic 25.12. Theorem 25.4 (a) cites "Theorem 1.5 below" for
   Theorem 25.5.
3. Chapters 26, 27 and 28 also keep draft numbers in their cross-references.
   Chapter 26 cites "Table 2.1", "Table 2.2", "Table 7.3", "Definition 3.1"
   and "section 7" for sections 26.2, 26.7 and Definition 26.8. Chapter 27
   cites "Table 3.1", "Theorem 3.3" (for Theorem 27.5) and "sections 27.1
   and 4". Chapter 28 cites "Proposition 1.3" (for Proposition 28.2),
   "Observation 1.1", "Section 1.7" and, in its file table, "Tables 2.1 and
   2.2" and "Tables 1.4 and 3.3".
4. Section 2.4: "There are 2,637 two-digit solutions with digits up to 60"
   counts both conventions together: 1,347 under `0^0 = 0` and 1,290 under
   `0^0 = 1` (`r6p_two_digit.py`). The text reads as one convention. The same
   holds for the 119 strings `(1, c)` and the 118 strings `(c, c)`. A note:
   35% of all 2-digit strings with digits up to 60 are solutions in some
   base, 21% up to 200 and 12.5% up to 600, per convention.
5. Section 17.2 compares conventions inside one ratio. "Forcing
   `w(x) == x` multiplies the count by 1955 / 103.5 = 18.9" divides a count
   under `0^0 = 0` by the mean of both conventions under `--perturb` (98 and
   109). Under one convention the ratio is 1955 / 98 = 19.9, against the
   model's 1891.4 / 111.8 = 16.9. The per-row comparison with the model on
   the same weights, which the conclusion uses, is not affected.
6. Section 21.1.6 still concludes that "the solutions are ordinary draws",
   from the offsets `(B - 1) g`. Lemmas 24.9 and 24.10 show that these
   near-solutions were mostly the solutions again, and the table of section
   26.4 marks the claim as withdrawn. Section 21.1.6 has no correction note.
7. Conjecture 10.3, second half ("infinitely many have
   `b > k + ln k + (1 - eps) ln ln k`"), uses the second Borel-Cantelli
   lemma, which needs the bases to be independent. The model assumes this;
   no test exists (question 106).
8. Section 14.7 lists as open "a proof of the set of lengths that positive
   integers take in base -n+i. For -1+i the data say lengths `== 1` or
   `4 (mod 8)`." Theorem 23.1 proved the case `-1+i`; the list has no mark.
