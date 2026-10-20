# Round 17: directions and questions

`questions.md` lists these questions as "Round 17". The file name follows
the older count of the files `questions-round3.md`, `questions-round5.md`
and `questions-round6.md`. The corrections made from its list of problems
are labelled "round 7 review".

A reading of the library after chapter 38, with chapters 29 to 38 read
closely and the questions 1 to 163 checked for overlap, produced this file.
The preface gives my reading of where the project stands, its blind spots,
and the assumptions that nobody has questioned. Then come 16 questions,
numbered 164 to 179, in six themes. Each question has the question, why it
matters, a first step, its kind, and my estimate of difficulty and payoff.
"Proposed workloads" groups them. "Problems found" lists errors,
inconsistencies and overstated claims in the library.

The leads come from quick runs by the questioner. The scripts are
`analysis/r7p_*.py`, and each prints the numbers quoted here. The numbers
are leads, not results.

## Preface: where the project stands

### What is settled

The three basic questions have moved unevenly.

- Which digit strings are never a solution? For 3 digits with two small
  digits and one large digit `x`, every position and parity is effectively
  finite except odd `x` in the middle (Corollary 38.9), and the 25 middle
  families with `pA` a square are bounded for prime powers (Theorem 38.2).
  The method is now clear: complete the square, factor in the quadratic
  field of the constant term `R`, and bound a linear form in the logarithms
  of an S-unit lattice whose covolume must stay below the exponent. Beyond 3
  digits there are coverings (Theorem 15.13), the square class
  (Theorem 8.3), the identity families, and conditional results under abc
  (Theorem 33.19). Nothing else.
- Which bases have no solution? Only computation, bases 19, 27 and 35 up to
  41, and a model that says about 20% of even and 9% of odd large bases. The
  2-digit narcissistic toy case is Landau's problem (Theorem 30.12), and
  section 32.2 judges the real question out of reach.
- How can the search be faster? The exact tree is optimal up to a factor
  about linear in `b` in an interval oracle (Theorem 27.5), and every order
  of revealing counts meets the entropy floor `1.638^b` (Theorem 27.2). The
  residue rule and the last-digit tests gave constant factors (chapters 31
  and 37). The Lean search proves the algorithm correct (section 37.5).

The model is in good shape. The refined model with forced top digits
accounts for every test named in advance (Fisher P = 0.74, section 34.4),
its Poisson law holds in the limit without Assumption R (Theorem 30.5), and
its expected count is the trace of a length matrix (Proposition 34.5).

### Blind spots

1. Drift toward 3 digits. Chapters 32, 36 and 38 spend most of the recent
   effort on strings with two small digits and one huge digit. The results
   are elegant, but by the model these strings carry about `10^-74` expected
   solutions beyond the lists (section 25.1.6), while a typical base has its
   one solution among strings of `b - 1` digits. The work answers basic
   question 2 for a slice that matters little to basic questions 1 and 3.
   The method also seems to stop at 3 digits (question 168).
2. No fresh data since round 6. Questions 104 and 105, the pre-registered
   census of bases 42 to 46 and the first `b`-digit solution under
   `0^0 = 1`, are still open. The exact census stops at base 43. Every
   statistical verdict of chapters 26 and 34 rests on bases 12 to 43.
3. No positive statements. The library proves non-existence, upper bounds
   and identity families. Under `0^0 = 1` the bases known to have a
   solution are, apart from the census, about `(ln X)^2` of the bases up to
   `X`. The model says more than 80%. Nothing in between is proven
   (question 170).
4. No decidability boundary. "Which strings are never solutions" is asked
   family by family, but nobody has asked which families can be decided at
   all. A short reduction suggests that general families cannot
   (question 164).
5. The search lower bounds are statements about a class of algorithms. They
   cover interval oracles and orders of revealing counts. "Only constant
   factors are left" is true inside that class. The brief for this round
   also called the exact search "formally verified in Lean". The algorithm
   is verified, in a separate functional implementation. The Rust engine
   that produced the census is not; its node counts agree with the Lean
   search in bases 2 to 12 (section 37.5).
6. Trust. Several "computer-assisted" theorems rest on C sieves checked by a
   second sieve on about 0.7% of the range (sections 36.7 and 38.6). Deep
   cited constants come from secondary statements, and for Laurent's
   `C2(10)` and Matveev's complex form the referee notes say that the
   original was not available. The Lean work found a real error in
   Lemma 36.1 (b). That is a reason to formalize more, not less.
7. Selection. The problem is famous because of 3435 in base 10. Base 10 is
   in every short-solution test, and it carries one of the four "generic"
   short exceptions on which the last unexplained residual rests
   (question 174).

### Assumptions that nobody questioned

- That "effectively finite" is progress toward "decided". Bounds such as
  `10^40`, `10^186` and `10^4178` are effective, but no computation reaches
  them, and the usual reduction step of Diophantine practice does not apply
  here at all (question 167).
- That the 3-digit method extends. The discriminant of the field that
  carries the argument grows with the number of digits, and a rough count
  says that 3 digits is the limit for Baker-type bounds (question 168).
- That the exact census is the gold standard. Model tests need a known miss
  rate, not exactness, and the questions of chapters 26 and 34 could use
  inexact runs at bases far beyond 43. Conversely, the model has never been
  tested at large bases on any statistic other than short solutions
  (question 173).
- That the unit of study is the base. One could equally count by digit
  string, by size of `n`, or by the number of distinct digit values. The last
  axis is where all known structure lives (question 171).
- That a solution is "generic" or "structural" independent of convention.
  Section 35.1.4 classifies one string differently under the two conventions
  (question 174).

### What I would do first

1. Question 164 (a): one page, and it changes what basic question 2 can
   mean.
2. Question 165: a cheap computation that already removed 10 of the 440
   middle families, and a proof that the others need global methods.
3. Question 169: one GPU run closes question 65 unconditionally.
4. Question 170: the first existence question about bases, the mirror image
   of Theorem 20.3.
5. Question 166: it names exactly what the middle position lacks.

## Theme XXI. What kind of problem this is

### 164. Which families of strings can be decided at all?

Call a template a `k`-digit string whose digits are polynomials with integer
coefficients in parameters `t_1, ..., t_m >= 0`. (a) Prove that no
algorithm decides whether a template has a member that is a solution in
some base. (b) Restrict to free-digit families: each digit is a constant or
a variable, and each variable occurs once. Is the existence of a solution
decidable for them? For one free digit and every `k`? Is there a number of
free digits beyond which it becomes undecidable?

Why: Each single string is decided by a finite computation (Propositions
1.3 and 11.1), so basic question 2 is a question about infinite families.
If general families are undecidable, the project needs a principled notion
of "family", and the case-by-case work of chapters 15, 25, 32, 36 and 38 is
a necessity, not a lack of cleverness. The free-digit families are exactly
the objects of those chapters: one free digit and fixed other digits. With
one free digit, decidability follows from effective finiteness, so
Corollary 38.9 already decides every 3-digit one-free-digit family except
odd `x` in the middle.

Attack (lead, unchecked): Part (a) seems to follow from Theorem 25.7 (ii)
and Matiyasevich's theorem. Take the template `(1, 2, 6 + 16 D(t)^2)` for a
polynomial `D` with integer coefficients. If `D(t) = 0` the string is
`(1, 2, 6)`, a solution in base 215. If `D(t) != 0`, the last digit
`x = 6 + 16 D^2` is even and at least `22 >= 2B + 4` with `B = 2`, so
`N = 4 x^x` is a square, and `R = 4 (w(1) + w(2) - x) + 2^2 = 24 - 4x =
-64 D(t)^2 != 0`. Theorem 25.7 (ii) then excludes every base, under either
convention. So the template has a solution exactly when `D` has a zero in
the natural numbers, which no algorithm decides. Check the argument, state
it as a proposition, and formalize the reduction: Theorem 25.7 (ii) is
already in `lean/Munchausen/ThreeDigits.lean`, and Mathlib has the
`Dioph` library. For (b), ask whether equations of the shape
`sum x_i b^(e_i) - sum x_i^(x_i) = C` can encode the exponential
Diophantine equations of Davis, Putnam and Robinson. Start with two free
digits in 3-digit strings, which is the open case of two large digits.

Kind: proof (logic and computability).

Estimate: (a) easy, a page, high payoff for the framing of basic question 2.
(b) hard. A decidability theorem for one free digit and every `k` would be
a major result; an undecidability theorem for free digits would be a
surprise.

### 165. Local and global obstructions for one free digit

Call a one-free-digit family locally soluble if for every modulus `M` some
admissible `x` (of the right parity) and some `b` satisfy the equation
modulo `M`, and the real root exceeds the digits for large `x`. (a) Which of
the 440 middle families `(p, x, q)` with `x` odd and `p, q <= 20` are
locally soluble? (b) For those that are, prove it, so that any finiteness
proof for them must be global. (c) Is there a family with one free digit,
no solution, local solubility everywhere and no Archimedean gap, for which
a Baker-type bound is provably necessary? The families of Theorem 32.3 are
candidates.

Why: Chapter 32 names three kinds of exclusion: local (coverings),
Archimedean (the gap of Theorem 25.7 (ii)), and global (Baker plus a
sieve). It says "I know of no covering of these families, and a heuristic
says there is none", but nobody checked. A covering closes a family at
once. If no covering can exist, these families are failures of a local to
global principle of an exponential kind, like Sierpinski numbers without a
covering set, and that is worth knowing before more Baker work. The sieves
of chapters 36 and 38 use 150 odd primes and never test powers of 2 or 3,
which are exactly the moduli of the coverings of chapter 15.

Lead (computed, `r7p_middle_local.py`): for each middle family and the
moduli `2^10, 3^6, 5^4, 7^3, 11^2, 13^2`, the share of odd `x` in
`[100001, 300001)` for which some `b` solves the equation modulo each
modulus, and modulo all six together. Ten families have share 0: the
strings `(p, x, 0)` with `p` odd under `0^0 = 1`. They fail modulo 2, since
`b (pb + x)` is even for odd `p` and `x` while `p^p + x^x + 1` is odd. This
is the parity rule of section 1.6, and it closes these ten families
outright (see "Problems found", item 3). The other 430 pass all six moduli
together, with shares from 0.0005 (`(2, x, 20)`) to 0.23 (`(1, x, 1)`),
median 0.034. So no covering exists among these moduli.

Attack: (a) Use exact periods. `x^x mod l^e` depends on `x` modulo
`l^e lambda(l^e)` for `x` prime to `l`, and is 0 for `l | x` once `x >= e`.
Test products of moduli as Theorem 15.13 did. (b) For each prime power,
find a smooth point and lift it by Hensel's lemma, as in Theorem 20.8; the
joint statement across primes needs the coupling of `x mod l` and
`x mod (l - 1)`. (c) Look in the last and leading positions too, where
finiteness is proven, for families that are locally soluble but have no
solution: there the Baker bound is the only proof.

Kind: proof and computation.

Estimate: (a) easy, (b) medium, (c) hard. Payoff: medium. It may close a
few families cheaply, it corrects the count of the open frontier, and it
says what kind of mathematics the rest needs.

### 166. Which conjecture closes the middle position?

The abc conjecture closes every 3-digit family with one large digit
(Theorem 33.16). Is a conjecture about linear forms in logarithms enough?
Let LW be the Lang-Waldschmidt conjecture: for
`Lambda = sum b_i log alpha_i != 0`,
`log |Lambda| >= -c(n, D) (log B + sum h(alpha_i))`, with the heights
entering as a sum, not a product. (a) Prove that LW together with GRH makes
the middle position finite for each pair of small digits. (b) Does LW alone
suffice? (c) Which further cells of question 168 (4-digit strings, for
example) does LW with GRH close, and which is the first cell it does not?

Why: The middle position fails because the relevant lattice has covolume
about `x L(1, chi)`, of the size of the exponent `x` (section 38.3.2).
Matveev's bound multiplies the heights, so the covolume costs a factor `x`.
With a sum of heights the cost is about `Reg + sqrt(h) log x`, which is at
most about `x L(1, chi)`, against the left side `(x/2) log x`. Under GRH,
`L(1, chi) << log log x`, and the inequality fails for large `x`. Without
GRH the comparison depends on the constant `c` of LW, since `L(1, chi)` can
be of size `log x`. So the middle position seems to need exactly "sum of
heights plus a small `L(1, chi)`", and that names the missing ingredient as
precisely as section 8.1 names the barrier for complexity. It would also
separate two conjectures: if LW with GRH closes 3 digits and the ends of 4
digits but not more, abc carries more than LW for this problem.

Attack: Take the exact statement of LW from M. Waldschmidt, Diophantine
Approximation on Linear Algebraic Groups (Springer, 2000), chapter 1, and
from S. Lang, Elliptic Curves: Diophantine Analysis (Springer, 1978),
introduction; check the dependence on `n` and `D`. Redo the proof of
Theorem 36.9 in the real field `Q(sqrt(x^2 + 4pA))`: the lattice of pairs
`(s, r)` with `J^s B^r` principal, a reduced basis, the fundamental unit as
a third logarithm, and `log(mu / mu')` as the linear form. Then try the
ends of 4-digit strings with the cubic field of question 168.

Kind: proof (conditional), transcendence theory.

Estimate: medium difficulty for (a) once the form of LW is fixed; (b) may
come down to the constant. Payoff: medium. Nothing unconditional, but a
clear statement of what the open case lacks.

### 167. Why no reduction step applies, and whether one could (speculative)

In Diophantine practice a Baker bound such as `10^40` on an exponent is cut
to a few thousand by the Baker-Davenport lemma or by de Weger's LLL
reduction, applied to a linear form whose algebraic numbers are fixed and
whose integer coefficients vary. Prove or refute: in every linear form of
chapters 32, 36 and 38, one of the algebraic numbers depends on `x`, so no
reduction of this kind applies. Then ask whether a reduction can be made
uniform over a family of algebraic numbers `delta(x)` of height `O(log x)`
that vary in a controlled way.

Why: The large digit `x` enters the string twice: as the base and exponent
of `x^x`, and linearly as a digit. After completing the square the second
appearance puts `x` into the constant term `R`, hence into the associate
`delta` of Step 1 of Theorem 32.2, the generators of Theorem 36.9, and the
number `alpha = (sqrt R + 1)/(sqrt R - 1)` of Theorem 38.7. Even where the
field is fixed (Theorem 32.2, Proposition 32.6, question 162), `delta`
moves with `x`. So every bound must be met by a sieve, and the sieve
reaches about `4 * 10^11`. This is why "effectively finite" and "decided"
differ by 29 to 175 orders of magnitude in this library, and the library
never says so. A uniform reduction would turn Theorem 36.9 into a
decision of the last position for small digits (question 149) and Theorem
38.6 into one for the leading position (question 161).

Attack: List every linear form in the three chapters and the dependence of
each algebraic number on `x`. For the last position, write
`log(rho_i / rho_i')` as a function of `x` and check whether the
continued-fraction step of Baker-Davenport can be done for a whole range of
`x` at once, for example when the class of `A` has bounded order. Search
the literature for reductions "with parameters" (families of Thue
equations, where the parameter also enters the field, are the nearest
case).

Kind: proof and method.

Estimate: the first part is easy and should be stated in the library. The
second is speculative and hard. Payoff: very high if it works, since every
effective bound in the library would become a decision.

## Theme XXII. Beyond three digits and one large digit

### 168. Is three digits the limit of the S-unit method?

For a `k`-digit string with fixed small digits and one large digit `x` at
position `i`, the equation is `P(b) = x^x + C` with `P` of degree `k - 1`
and `x` a coefficient of `P`. Let `K` be the field of a root of the
polynomial that carries the argument. Determine, for every `k` and `i`, the
size of `|disc K|` as a power of `x`, and prove or refute: the argument of
Theorems 36.9 and 38.6 (an S-unit lattice whose covolume is below the
exponent) works exactly when `sqrt(|disc K|) = o(x / (log x)^c)`. Which
positions satisfy this?

Why: If the method stops at 3 digits, then basic question 2 for 4 or more
digits needs a new idea, abc, or LW (question 166), and the project should
know it before investing in 4-digit Pell or Thue work (section 32.1.7,
question 131). A rough count (lead below) says that the two ends of 3-digit
strings are the only cells where the method works unconditionally, that the
3-digit middle and the two ends of 4-digit strings are the borderline cases
(covolume of the size of the exponent), and that everything else is out of
reach even under LW.

Lead (heuristic, by the questioner): the discriminant of
`a_d T^d + ... + a_0` contains `d^d a_d^(d-1) a_0^(d-1)`, so when `x` is the
constant term (last position) or the leading coefficient (leading
position), `|disc| ~ x^(d-1)` with `d = k - 1`. When `x` is a middle
coefficient the power is higher: `x^2` for the 3-digit middle, `x^3` for
the middle positions of 4 digits. Then `h Reg` is about `sqrt(|disc|)`,
which is `x^(1/2)` for the ends of 3 digits (the two closed cases), `x` for
the 3-digit middle (open) and the ends of 4 digits, and `x^(3/2)` or more
beyond. For a 4-digit string with `x` last, the conjugates of `b - beta` in
the cubic field give a linear form of size `x^(1/3 - x/3)`, so the
small-form side of the argument is there; only the covolume is too large.
Special prefixes with a fixed field (the binomial prefixes of section
32.1.7) escape the count.

Attack: Make the table of exponents exact, with the ring of integers and
the S-unit rank in each cell. Then try the borderline cell with the most
structure, the 4-digit leading position, where `x theta` with
`x theta^3 + q theta^2 + r theta = A` is integral and its norm is divisible
by a power of `x`, as `theta = (q + sqrt R)/2` was in Lemma 38.5.

Kind: proof.

Estimate: the table is easy; a proof that the method cannot work is a
meta-statement and needs care. Payoff: high for planning.

### 169. The next 3-digit solution, unconditionally

Run the sieve of Theorem 25.11 over every 3-digit string with digits up to
46,700, in all positions, about `10^14` strings. Is any string other than
the known seven a solution?

Why: Question 65 is answered only heuristically. Theorem 25.11 proves that
`(1, 6, 46666)` is the next 3-digit solution after `(1, 7, 1)` among
strings with at most one digit above 200, and section 25.2.3 leaves the
strings with two digits in `[201, 46666]` to a heuristic (`10^-3294`
expected). A complete run makes it a computer-assisted theorem: every base
below `46666^23333 - 3`, about `10^108941.8`, has its 3-digit solutions
known, under `0^0 = 1`. It is also the only cheap result about two large
digits, the case that abc leaves open (Proposition 33.20) and that no
unconditional method touches.

Attack: `r5f_sieve3.c` tested `1.36 * 10^10` strings in about 15 minutes on
one thread, so `10^14` strings take about 77 thread-days on the CPU. The
kernel (residues of `w(d)` modulo 108 primes, a quadratic residue test) is
a natural fit for the GPU of chapter 28. Skip the `5.6 * 10^9` strings with
at most one digit above 200, which Theorem 25.11 covered. Check every
survivor with exact integers, and rerun a random 1% slice with a second
sieve on different primes, as section 38.6 did.

Kind: search engineering and computation.

Estimate: easy to medium (porting and a run of about a day on the GPU).
Payoff: medium to high: a clean, citable theorem and the first statement
about two large digits.

## Theme XXIII. Existence and the bases

### 170. How many bases provably have a solution?

Let `E_m(X)` be the number of bases `b <= X` with a nontrivial solution
under `0^0 = m`. The model says that `E_1(X)` is more than `0.8 X`. What
lower bound can be proven? (a) Under `0^0 = 1`, prove
`E_1(X) >= (ln X)^A` for every `A`, or `E_1(X) >= X^c` for some `c > 0`.
(b) Prove the converse statement that any such bound needs solutions of
length at least about `c ln X / ln ln X`, and state it beside Theorem
20.3. (c) Find a construction under `0^0 = 1` that pays for zeros in many
bases.

Why: Basic question 1 asks which bases have no solution. The library has
only upper bounds on the bases with short solutions (Theorems 20.3 and
35.12) and the near-solutions of Theorem 35.13. It has never asked the
mirror question: how many bases is a solution known to exist in? The answer
today is small, and the gap between the conventions is large. That gap is
a fact about the digit 0 that the model does not see.

Lead (computed, `r7p_bases.py`): under `0^0 = 1` the bases `b <= X` with a
2-digit solution number 35 for `X = 10^6`, 84 for `10^12`, 466 for `10^48`,
1,208 for `10^100` and 2,937 for `10^200`, roughly `(ln X / ln ln X)^2`.
Apart from the census of bases up to 45, the short-solution lists of
chapter 3 (a handful of bases such as 91, 215, 904 and 48), the 11-digit
chain of base 64 and the members of the identity families (one per level
of a tower), these are all the bases known to be nonempty. Under `0^0 = 0`,
every odd square `r^2 >= 9` has the self-paying solution
`(r, 0, ..., 0)` with `(r - 1)/2` zeros, since `r * r^(r-1) = r^r`. So
`E_0(X) >= sqrt(X)/2` for large `X`, against polylog for `E_1`.

Attack: (b) is a counting argument: a string with `k` digits is a solution
in at most one base, and there are at most `C(X_k + k, k)` strings with
digits up to `X_k(X)`. (c) Under `0^0 = 1`, a self-paying digit `a` at
position `k` leaves `k` zeros to pay. Look for gadgets of positive balance
exactly `k`, such as a digit `s` at position `i` with
`s b^i - s^s = k`, and count the bases where gadget and self-paying digit
coexist, starting from the chains of Theorem 15.14 and question 88.
(a) needs either many constructions or an analytic argument, which would
amount to equidistribution of `F` in many bases at once.

Kind: proof.

Estimate: (b) easy; (c) medium; (a) very hard for `X^c`, perhaps medium for
`(ln X)^A`. Payoff: high. It is the first positive statement about basic
question 1.

### 171. A census by the number of distinct digit values

Let `K(s)` be the number of distinct nonzero digit values of a string. Find
every solution with `K <= 3` (any number of zeros, any length) in all bases
up to `10^4`, or as far as the method reaches, under both conventions. Are
all of them structural (self-paying digits and blocks, families, chains),
apart from a short list in small bases?

Why: All known structure lives at small `K`: self-paying strings have
`K = 1` or 2, the family of Theorem 25.5 has `K = 2`, the 3-digit
binomial members have `K <= 3`, and the chain of base 64 has `K = 4`.
The census by length cannot see this axis, because the strings with small
`K` are a tiny share of the strings of each length. A census by `K` is a
new kind of fresh data. It may find new structured solutions under
`0^0 = 1`, which bear on whether `N_1(b)` is bounded (section 7.4) and on
question 170, and it tests Conjecture 25.8 on a set of strings that is
infinite in length.
Theorem 35.12 says that almost all bases have no solution of length up to
`(ln b)^C` with few large digits, so the hits should be rare and
structural.

Lead (computed from `output/b2-41-*.txt`): among the census solutions with
at least 3 digits, `K` ranges from 2 to 27 under `0^0 = 1`. Seven have
`K <= 3`. Three of the four "generic" short exceptions of section 35.1.4
have `K = 3`: 3435, `(3,3,6,6,1)` in base 13 and `(2,6,0,3,6)` in base 14.
Under `0^0 = 0` every solution with at least 5 digits and `K <= 3` in bases
2 to 41, except `(2,2,3,5,2)` in base 6, is a block pair or a self-paying
string.

Attack: For `K` values `v_1 < ... < v_K` with counts and a number of zeros,
`F` is a sum of `K + 1` terms, and the top digits of `F` are forced by the
largest value and its count. Write a tree over the values in decreasing
order, as `fast` does over counts, with the interval test, but with at most
`K` nonzero counts. Its size is polynomial in `b` for fixed `K`. Validate
against the census up to base 41.

Kind: search engineering and computation.

Estimate: medium. Payoff: medium, with a chance of new families.

## Theme XXIV. The model as a map

### 172. Is the multiset map lumpable?

Let `phi_b` send a digit multiset `c` to the multiset of digits of `F(c)`.
Solutions are the fixed points of `phi_b` with at least 2 digits, and the
basic and refined models are traces of matrices obtained by lumping
`phi_b` over partitions of the multisets: by length (Proposition 34.5), by
length and residue modulo `b - 1` (Proposition 34.10). For bases 8 to 14,
compute `phi_b` on every multiset. For a sequence of finer partitions
(length; residue; top digit of `F`; top two digits), how close is the
trace of the lumped matrix to the true number of fixed points, and how far
is `phi_b` from being lumpable (the spread of the rows inside a class)?

Why: Chapter 34 concludes that no third kind of correction is needed "at
the present precision", which is the precision of near-solutions at bases
12 to 26. An exhaustive computation of the map at small bases is a test
with no sampling error at all, in the language of dynamics: a partition is
good when the map is nearly Markov with respect to it. The coarsest good
partition is "what the arithmetic of `x^x` sees". If adding the top digits
makes `phi_b` nearly lumpable, the refined model is complete in a precise
sense. If not, the defect locates the missing structure. The same data give
the full functional graph: cycles (chapter 15), image share (section 26.7),
in-degrees and component sizes, against random mappings with the same
lumped law.

Attack: The multisets of at most `b` digits number about `C(2b, b)`: 2.7
million at `b = 12`, 40 million at `b = 14`. `F` fits in 64 bits up to
`b = 14`. Index multisets by their rank, compute `phi_b` in C or numpy, and
build the lumped matrices. Compare their traces with the census of
`output/`.

Kind: computation, cross-field (Markov chains and lumpability, random
mappings).

Estimate: easy to medium. Payoff: medium. It turns "no third correction" from
a statistical verdict into an exact one at small bases.

### 173. Testing the model at large bases

Every count of the library is tested at bases up to 43, and the short
solutions at large bases only test the root heuristic. Find a statistic of
long strings that can be computed exactly at bases 60 to 300 and that the
model predicts. Candidate: the number of nodes of the exact tree at each of
its top levels, down to the level where it passes about `10^9`, against the
model's level counts (section 9.1, `tree_model.py`, with the forced top
digits of sections 11.2 and 23.5).

Why: The model's large-base claims (about one solution per base, 55% with
`b - 1` digits, 20% and 9% of empty bases, base 100 with one solution) rest
on its laws for the large-digit counts and the top digits of `F`. The top
levels of the tree measure exactly those laws, at any base, since they are
small. A mismatch at base 200 would matter more than any anomaly at base
26. The construction of Theorem 35.13 gives a second handle: it produces
nodes that survive to depth `0.13 b` to `0.5 b` (Table 35.5.2.1), and the
model predicts how many such nodes exist.

Attack: Count the nodes of the top levels by building work units at
increasing depth without running them (check whether `fast` can stop after
the units; if not, add an option). Compare level by level with the model,
and with the per-level growth `C(b, kappa b)` of section 10.1.

Kind: computation.

Estimate: easy to medium. Payoff: medium; the only test of the model where
it makes its boldest claims.

### 174. Selection and classification in the short-solution residual

Recompute the short-solution tests of sections 10.5 and 35.1.4 with two
rules fixed in advance: (a) leave out base 10, the base that defines the
problem; (b) classify a string as structural by a rule that does not depend
on the convention, for example "contains an exact self-paying block or a
self-paying digit, or is a family member". Does any short-solution excess
survive?

Why: Section 35.1.4 ends with "under `0^0 = 1` a generic excess of about 3
times remains (4 against 1.35)", P = 0.048, and calls it unexplained. Two of
the four strings deserve a second look. 3435 is in base 10, and base 10 is
in the data because 3435 made the problem famous. `(3,3,6,6,1)` in base 13
is called generic under `0^0 = 1`, while the same section calls
`(3,3,6,6,0)`, `(3,3,6,6,1)` a block pair under `0^0 = 0`. The string has
no zero, so it is the same solution under both conventions, and chapter 22
shows that it is the exact block `(3,3,6,6)` at shift 1 followed by the
self-paying digit 1. With one correction the count is 3 against 1.35,
`P(>= 3) = 0.155`. With both, 2 against about 1.3, `P(>= 2)` about 0.37.

Attack: Write the two rules down, recompute the expectations without base
10 with `r6h_shortref.py`, and apply the rules to the 5-digit excess of
section 22.4.3 and to the ledger of section 34.4. Record whether each group
was named before or after the data.

Kind: computation (statistics).

Estimate: easy. Payoff: low to medium; it probably closes the last
unexplained residual, and it sets a rule for future tests.

## Theme XXV. Lower bounds and what lies outside them

### 175. Search lower bounds in other models

(a) Prove the fooling-set bound of Theorem 27.5 asymptotically: for every
large `b`, some level has `N_k >= W_b / poly(b)`, where `W_b` is the widest
level of the exact tree. (b) Extend the oracle: let a query also reveal
`S mod (b - 1)` once the counts are complete, or `S mod b^j` once the
counts that fix it are known (Proposition 27.8). Does the bound survive?
(c) Proof complexity: the statement "base `b` has no `d`-digit solution" is
the infeasibility of one linear equation
`sum over i, x of y_(i,x) (x b^i - w(x)) = 0` in 0/1 variables with one
`y_(i,x) = 1` per position `i`. Prove a lower bound `2^(Omega(b))` for its
refutations in resolution (with a standard encoding of the arithmetic) or
in cutting planes.

Why: Section 8.1 shows that an unconditional lower bound for every
algorithm would prove P != NP. Lower bounds for restricted models are not
blocked by that barrier, and they are the honest form of "only constant
factors are left". The comparison of Theorem 27.5 with the widest level is
computed only up to base 21. CaDiCaL's conflicts grow 1.96 per base
(section 27.1), a measurement of resolution proof size that asks for a
theorem. Cutting planes can reason with the
linear equation directly, and they are the proof system in which a modular
argument such as Theorem 31.1 could be short.

Attack: (a) Use the model's level law of section 10.1 and a second-moment
argument for the fooling set. (b) Find the fooling vectors of section 27.3
whose sums agree modulo `b - 1` and modulo `b^j`; the residue removes a
factor at most `b - 1`, so the bound should survive up to a polynomial.
(c) The equation is a multiple-choice knapsack of density about 1 (section
30.4). Look at known lower bounds for knapsack and subset-sum
infeasibility in cutting planes (for example via feasible interpolation),
and at the parity and pigeonhole lower bounds of resolution.

Kind: proof (complexity theory).

Estimate: (a) medium, (b) medium, (c) hard. Payoff: medium; (c) would be
the first unconditional exponential lower bound for this problem in any
proof system.

### 176. Atypical nodes: can information outside the interval certify them?

The exact tree grows like `1.89^b` (tending to `2^b`), the likely part
like `1.638^b`, and the `--zscore` search like `1.71^b`. The difference
is the atypical nodes, 83% of the tree at base 23 (section 6.2). For the
nodes that `--zscore 3.4 --zlaw cond` cuts, how is the exact work below
them distributed, and is there an exact test, using information that the
interval oracle of Theorem 27.5 does not give, that is cheap on exactly
those nodes?

Why: Theorem 27.5 says that no method that learns only through intervals
beats the exact tree by more than a polynomial factor. So a speedup in the
exponent must use other information. Atypical nodes are where such
information could be cheap: many copies of a few large digits make `S`
nearly a sum of a few known powers, so its middle and low digits may be
computable early, and the last-digit masks of chapter 37 may be dense
there. Even a partial success changes the exponent: `(1.89/1.71)^46` is
about 100 at base 46.

Attack: Instrument `fast` to run the exact search below every node that the
z-score rule would cut, at bases 24 to 30, and record the subtree size with
the node's type (free slots, decided counts, z-score). Fit which features
predict empty subtrees. Then test candidate rules: the digits of `S` in the
lanes just below the known prefix, computed from the dominant weights; the
masks of section 37.1 at more lanes; a residue modulo `b^j` when the
undecided digits are few.

Kind: search engineering.

Estimate: hard; most attempts will give constant factors. Payoff: high if
it works, since it is the only route left to a better exponent on
classical hardware.

## Theme XXVI. Trust

### 177. A fully formal finiteness theorem for an exponential family

Formalize in Lean, with no cited theorem as a hypothesis, Theorem 38.2 and
Corollary 38.3 for the families `(1, x, 1)`, `(1, x, 0)` (under `0^0 = 0`)
and `(1, x, 3)`: for an odd prime power `x`, `(1, x, 1)` is a solution only
for `x = 3` (base 4) and `x = 7` (base 904), and `(1, x, 3)` with `x`
prime to 5 never is (Theorem 38.2 gives `x <= 3,438`, and an exact check
covers the rest).

Why: Every finiteness theorem for an exponential family in the library
rests on cited deep results (Baker, Matveev, Laurent, primitive divisors)
or on long sieves, except Theorem 38.2, which needs only ideal arithmetic
in a real quadratic field, the integrality of a trace, and one numerical
gap: `2 sinh 2 = 7.2537` for `k = 1`, so `X_sq = 7.64`, and `x <= 7` is a
finite check. For `(1, x, 3)` the gap `g-` comes from `e^10`, and the check
below `X_sq` needs one non-residue certificate for each of the odd prime
powers up to 3,438. The powers of 5 need Proposition 32.6 and stay out.
This would be the first end-to-end machine-checked theorem of its kind,
including the exceptional solution in base 904. The Lean project already
has the setting (`FieldFamily.lean`, `ThreeDigits.lean`), and Mathlib has
Dedekind domains, class groups and bounds on `exp`.

Attack: Work in the ring of integers of `Q(sqrt(x^2 + 4k^2))`; for `k = 1`,
`theta = (x + sqrt(x^2 + 4))/2` is a unit and `theta + 1` has norm `x`, so
no class group is needed. Prove Lemma 38.1 (c), (d) with ideal
factorization, then Steps 1 to 4 of Theorem 38.2. Bound `e^2` and `e^10`
by Mathlib's series bounds for `exp`. For the finite check, compute
`x^x mod l` by repeated squaring in the kernel and record a witness prime
for each `x`.

Kind: formalization.

Estimate: medium to hard (the ideal arithmetic in Mathlib is the hard
part). Payoff: medium to high for trust, and it tests whether the library's
style of argument survives formalization, as Lemma 36.1 (b) did not.

### 178. The trust chain of the census and the sieves

(a) Can the verified search of `lean/Munchausen/Search/` be refined, with a
proof, into an implementation fast enough to certify the census of bases
up to 20 or 24 by compiled code? (b) Can `fast` emit a per-unit trace
(unit, node count, solutions) that the Lean search checks on random units
at bases 25 to 33? (c) Can the sieve kernels of chapters 32, 36 and 38 be
proven sound in Lean (the period of `x^x mod l`, 0 as a square, the wheel)
and run from Lean, or emit certificates for random slices?

Why: The census (bases 13 to 43) and eight computer-assisted theorems
(25.11, 32.3, 32.7, 33.6, 36.6, 36.8, 38.3, 38.8) rest on unverified code.
The second sieves check about 0.7% of the new ranges (section 38.6). The
Lean search agrees with the Rust node counts in bases 2 to 12 only, and the
Rust engine builds its work units without the tests. Every finding of the
library about the model depends on the census being right.

Attack: For (a), write an array-based search in Lean and prove it equal to
the functional one, step by step, as `settle_eq_of_le` already does for one
loop. For (b), add a `--trace` option to `fast` and a Lean `#eval` checker.
For (c), start with the formula for `D` and the reduction of `x^x` modulo
`l`; the rest of the C program is a loop.

Kind: formalization and engineering.

Estimate: medium for (b) and (c), hard for (a). Payoff: medium; it moves
the census from "tested" to "checked".

### 179. An audit of the cited constants and a literature search

Obtain the original papers and check every use of: Laurent's Corollary 2
with `(m, C2) = (10, 25.2)` (Theorem 38.7, section 18.1.4); Matveev's
Corollary 2.3 in the real and the complex form (Propositions 32.6, 32.7,
Theorems 36.9, 38.6); the Bugeaud-Laurent 2-adic bound (Theorem 32.1); the
Lehmer tables of Bilu, Hanrot and Voutier (Lemma 36.3); Hooley's constant
`3/pi` (Corollary 30.13); and the Crocker-Somer bounds (section 30.2.1).
Then search the literature for prior results on `y^2 = a x^x + c`,
`b (pb + x) = x^x + A` and divisors of `x^x + 1` near `x^(x/2)`.

Why: For Laurent's bound, Matveev's complex form and the Crocker-Somer
bounds the library says that the original was not seen, and the other
constants were also taken from secondary statements. A wrong
hypothesis or constant would void several "proven" rows of the README at
once, and none of the second sieves would notice. The literature search may
find that parts of chapters 16, 18, 36 or 38 are known, or that the middle
position has a known partial answer.

Attack: Library access, a list of each theorem's hypotheses as used, and a
check row by row. For the search: MathSciNet and zbMATH for `x^x` in
Diophantine equations, and the literature on Lebesgue-Nagell equations with
varying exponent.

Kind: referee work and literature.

Estimate: easy. Payoff: medium; it protects about ten proven results.

## Proposed workloads

Workload 1: the shape of the problem (proofs and a small computation, two
days).

1. Question 164. The reduction for templates, then free digits.
2. Question 165. Coverings and local solubility of the middle families.
3. Question 166. The middle position under LW and GRH.
4. Question 168. The table of discriminants, and the limit of the method.
5. Question 167, first part. Which linear forms move with `x`.

Why this grouping: together they say what kind of mathematics basic
question 2 needs beyond 3 digits, before more effort goes into it.

Workload 2: fresh data (GPU and CPU, a few days).

1. Question 169. The 3-digit sieve over `10^14` strings.
2. Question 171. The census by distinct digit values.
3. Question 173. The top levels of the tree at bases 60 to 300.
4. Questions 104 and 105 of round 6, still open.

Why this grouping: the library has had no fresh data since base 43, and
each of these runs can settle a statement.

Workload 3: existence and the model (proofs and exhaustive computations).

1. Question 170. Bases that provably have a solution.
2. Question 172. Lumpability of the multiset map.
3. Question 174. Selection and classification.
4. Question 175. Lower bounds in restricted models.
5. Question 176. Atypical nodes.

Workload 4: trust (Lean and referee work).

1. Question 179. The audit, first, since it is cheap.
2. Question 177. A fully formal exponential-family theorem.
3. Question 178. The census and the sieves.

## Problems found in the library

1. README, main results (chapter 36 item), and the README chapter table:
   "an effective bound independent of `q`: `x <= max(X_B(p), W + q^2/(4p))`"
   and "uniformly in the second digit". Since `W = w(p) + w(q)`, the bound
   grows like `q^q`. Only `X_B(p)`, the bound beyond the real range, is
   independent of `q`; for `x <= W + q^2/(4p)` the field of `R` is real, and
   nothing beyond the finite range is known, uniformly or not. The
   "Uniformity" paragraph of section 36.3 says this correctly. The same
   overstatement is in the update of chapter 36 to section 7.2 ("uniformly
   in `q`") and in the correction of chapter 36 to section 25.1.4.
2. README, main results (chapter 38 item): "every 3-digit family with one
   large digit is finite, effectively, except an odd large digit in the
   middle (Corollary 38.9)". Corollary 38.9 leaves out the leading families
   `(x, 0, 0)` and `(x, 0, 1)` under `0^0 = 0`, which have infinitely many
   solutions (`x b^2 = x^x` for odd `x >= 5` and even squares). The README
   drops the exception.
3. Proposition 36.11 and section 38.3.2: of the 440 middle families, "415"
   have `pA` not a square and are open except for density 0. Ten of them,
   `(p, x, 0)` with `p` odd under `0^0 = 1`, are never solutions by the
   parity rule of section 1.6: `b (pb + x)` is even, `p^p + x^x + 1` is odd.
   So 405 non-square families are open. The sieves of sections 36.5 and
   38.5 use only odd primes and did not notice (question 165).
4. Sections 7.2 and 8.2 are stale. The chapter 36 updates there say that
   the leading position (and in 8.2 "the middle and leading positions")
   remain open. Chapter 38 closed the leading position, but its list of
   corrections does not include these two sections. The status table of
   section 8.7 does not mention chapters 36 and 38 in its row on short
   solutions.
5. README, computed results (chapter 37 item): "leave 0.52 to 0.60 of the
   nodes of the residue rule in bases 15 to 33". Table 37.2.5 gives 0.660
   at base 15. The range 0.52 to 0.60 holds from base 20 on, as section
   37.2.4 says.
6. Section 8.7, row "fast exact search": "equivalent in difficulty to P vs
   NP". Section 8.1 shows that a superpolynomial lower bound would prove
   P != NP and NP-hardness would prove P = NP. A faster exponential
   algorithm, say `1.5^b`, is not blocked by either, and a proof that
   `1.638^b` is optimal would be at least as hard as P != NP, not
   equivalent to it. The row conflates "polynomial" with "faster".
7. Section 35.1.4 and Heuristic 35.4 classify `(3,3,6,6,1)` in base 13 as a
   generic short exception under `0^0 = 1`, but list `(3,3,6,6,0)`,
   `(3,3,6,6,1)` as a structured block pair under `0^0 = 0`. The string
   has no zero and is the same solution under both conventions; chapter 22
   shows it is the exact block `(3,3,6,6)` at shift 1 followed by the digit
   1. With a consistent rule, the residual under `0^0 = 1` is 3 against
   1.35 (`P = 0.155`), not 4 against 1.35 (`P = 0.048`). With base 10 also
   left out for selection, it is 2 against about 1.3 (question 174).
8. Remark after Theorem 38.2: "effective, with no a priori bound on the
   precision needed". An effective transcendence measure for `e` (Mahler,
   1932, and later explicit forms) bounds
   `|k^a E^2 - N E -+ k^a|` from below for `E = e^(2ke)`, so an a priori
   precision exists. Minor; the bound is effective in the strong sense.
9. Numbering of rounds. `questions.md` numbers its sections "Round 7" to
   "Round 16" for questions 111 to 163, while the files
   `questions-round3.md`, `questions-round5.md`, `questions-round6.md` and
   this one count the full-library readings. The questions of this file
   appear in `questions.md` as "Round 17". One numbering would be clearer.
10. Section 32.1.4: "Three values passed every prime: `(3,1,2)`, `(3,2,2)`
    and `(3,2,2)` with `x` in the middle" reads as a duplicate; it means the
    string `(3,2,2)` read with `x` last and with `x` in the middle. In the
    proof of Proposition 32.7, "For `p, q <= 10` The only survivors" has a
    stray capital.
11. The brief for this round said that "the exact search is formally
    verified in Lean". Section 37.5 is precise: the Lean search is a
    separate functional implementation of the algorithm, proven complete
    and sound, with node counts equal to `fast --unit-depth 0` in bases 2 to
    12. Summaries outside the library should say "the algorithm is
    verified", not "the search is verified" (question 178).

Status (round 7 review, 2026-10-20). All eleven problems were checked and
fixed in the library, and in the exposition where the same claim appears;
the corrections are dated "round 7 review". Two numbers differ from the
list. In item 7, base 10 contributes 0.26 of the expectation 1.35, so
without base 10 the residual is 2 against 1.08, P = 0.29 (not "about
1.3"). In item 3 a check modulo each one of 2, 3, 4, 5, 7, 8, 9, 11, 13
and 16 finds no local obstruction beyond the 10 parity families.