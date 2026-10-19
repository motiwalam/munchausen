# 13. The general problem is NP-complete, and a Poisson law

This chapter answers questions 27 and 22 of `questions.md`. Part 1 proves that
the Munchausen problem with arbitrary weights is NP-complete, and that its
counting version is #P-complete under parsimonious reductions. It then
explains what this means next to section 8.1. Part 2 proves a Poisson limit
theorem for the number of solutions in the probabilistic model of chapter 5,
with the twins, the shared zero-free solutions and the digit-sum residue
built in, and compares the predicted correlation of `N_0` and `N_1` with the
data.

Scripts: `analysis/thy_reduction.py` (part 1) and `analysis/thy_poisson.py`
(part 2).

## 13.1 The generalized problem

### 13.1.1 Definitions

GEN is the following decision problem.

- Input: a base `b >= 2` in unary, and nonnegative integers
  `w(0), ..., w(b-1)` in binary.
- Question: is there an integer `n >= b` with `F_w(n) = n`, where `F_w(n)`
  is the sum of `w(x)` over the base-`b` digits `x` of `n`?

The input size is `s = b + sum over x of (number of bits of w(x))`. The real
problem `L_m` of section 8.1 is the family of instances `w(x) = x^x`,
`w(0) = m`. Write `W = max w(x)`.

For a digit string, its multiset is the vector of counts `c_x` of its nonzero
digits. If `w(0) = 0`, then `F_w(n) = sum c_x w(x)` depends only on this
multiset, and `n` is a solution exactly when the nonzero digits of the
number `N = sum c_x w(x)` have the multiset `c`.

Lemma 13.1 (length). Let `n` have `D >= 2` digits and `F_w(n) = n`.

- (a) `b^(D-1) <= D W`. So `D <= max(6, 2 log2 W + 1)`.
- (b) If `W < b^M` and `b > M + 2`, then `D <= M + 1`.

Proof. `n >= b^(D-1)`, and `F_w(n)` is a sum of `D` weights, each at most
`W`. This gives the first inequality. For (a), `b >= 2` gives
`2^(D-1) <= D W`. For `D >= 7` we have `2^(D-1) / D >= 2^((D-1)/2)`, because
this holds at `D = 7` (`64/7 > 8`) and the left side grows faster. So
`2^((D-1)/2) <= W`. For (b), suppose `D >= M + 2` and put
`t = D - M - 1 >= 1`. Then `b^(D-1) <= D W < D b^M` gives
`b^t < D = t + M + 1`. But
`b^t >= t b >= t + (b - 1) > t + M + 1`. This is a contradiction.

Proposition 13.2. GEN is in NP.

Proof. The certificate is the digit string of `n`. By Lemma 13.1(a) it has
`O(log W) = O(s)` digits, each with at most `log2 b + 1` bits. The verifier
computes `n` and `F_w(n)` with integers of `O(s log b)` bits, in polynomial
time.

### 13.1.2 The reduction

SUBSET-SUM: given positive integers `a_1, ..., a_k` and an integer
`T >= 0`, is there a set `S` of indices with `sum over i in S of a_i = T`?
#SUBSET-SUM counts these sets.

The construction. Let `B = max(T, a_1, ..., a_k, 1)`. Choose a base `b`, a
prime `p` and an integer `L >= 0` such that

- (R1) `p` divides `b - 1`;
- (R2) with `D* = L + 2k + 4`: `2 D* <= b` and `p > D*`;
- (R3) `b^(L+1) > D* p B`.

The digits get three roles.

- Item digits `x_i = b - 1 - i` for `i = 1, ..., k`, at the positions
  `P_i = L + 2i`.
- The mandatory digit `z = b - 2 - k`, at the position `P_z = L + 2k + 2`.
- All other nonzero digits are prohibited. This includes `b - 1`.

The weights are

    w(0)   = 0,
    w(x_i) = x_i b^(P_i) + p a_i,
    w(z)   = z b^(P_z) - p T,
    w(y)   = y + 1                  for every prohibited y.

The designated digits `z, x_1, ..., x_k` all lie in the range
`b/2 < x <= b - 2`, because `b >= 2 D* >= 4k + 8`. Every weight is below
`b^(P_z + 1)`.

Parameters exist and are found in polynomial time. Let `beta` be the bit
length of `B`. Take `p` the smallest prime with `p >= 4 (beta + 2k + 5)` and
`p >= 64`, then `b = p + 1` and `L` the least integer with `b^L >= p B`.
Bertrand's postulate gives `p = O(k + beta)`, so `b` is polynomial in the
input size, and `p` is found by trial division. Then (R1) holds. We have
`L <= log2(p B) + 1 <= log2 p + beta + 1`, so
`D* <= log2 p + beta + 2k + 5 <= p/8 + p/4`, which gives (R2). (R3) holds
because `b^(L+1) >= b p B > D* p B`.

Theorem 13.3. For every instance, the solutions `n >= b` of the weight table
above correspond one to one to the sets `S` with `sum over S of a_i = T`. The
set `S` corresponds to

    n_S = z b^(P_z) + sum over i in S of x_i b^(P_i).

Proof. First, `n_S` is a solution. Its nonzero digits are `z` and the `x_i`
with `i` in `S`, each once, at distinct positions. So
`F_w(n_S) = n_S + p (sum over S of a_i - T) = n_S`. Also `n_S >= b^(P_z) >= b`.
Distinct sets give distinct numbers.

Conversely, let `n >= b` be a solution with `D` digits and nonzero multiset
`c`, so `n = N = sum c_x w(x)`. For a designated digit `x` write
`w(x) = x b^(P_x) + e_x`, with `e_(x_i) = p a_i` and `e_z = -p T`.

Step 1 (length). All weights are below `b^M` with `M = P_z + 1`, and
`b >= 2 D* > P_z + 3 = M + 2`. By Lemma 13.1(b), `D <= P_z + 2 = D*`.

Step 2 (no prohibited digit). The digit sum of `N` is `sum c_x x`, because
the nonzero digits of `N` form `c`. Every integer is congruent to its digit
sum modulo `b - 1`, hence modulo `p` by (R1). So

    0 == N - sum c_x x == sum c_x (w(x) - x)   (mod p).

For a designated digit, `w(x) - x = x (b^(P_x) - 1) + e_x == 0 (mod p)`,
because `b == 1` and `p` divides `e_x`. For a prohibited digit,
`w(y) - y = 1`. So the number `c_pro` of prohibited digits of `n` satisfies
`c_pro == 0 (mod p)`. But `0 <= c_pro <= D <= D* < p` by (R2). So
`c_pro = 0`: every nonzero digit of `n` is designated.

Step 3 (the error is not negative). Put `H = sum over designated x of
c_x x b^(P_x)` and `E = sum c_x e_x`, so `N = H + E`. There are at most `D*`
designated digits, so `|E| <= D* p B < b^(L+1)` by (R3). If every count were
0, then `N = 0`, which is not `>= b`. So `H >= b^(L+2)`, and `H` is a
multiple of `b^(L+2)`, because every `P_x >= L + 2`. Suppose `E < 0`. Then
`N == -|E| (mod b^(L+2))`, and `N mod b^(L+2) = b^(L+2) - |E|` lies strictly
between `b^(L+2) - b^(L+1)` and `b^(L+2)`. So the digit of `N` at position
`L + 1` is `b - 1`, a prohibited digit. This contradicts Step 2. So
`E >= 0`.

Step 4 (no repeated digit). Each count satisfies `c_x <= D <= D*`, so
`c_x x < D* b <= b^2`. Write `c_x x = h_x b + l_x` with digits `h_x, l_x`.
The positions `P_x` differ by at least 2, so `H` has the digit `l_x` at
`P_x`, the digit `h_x` at `P_x + 1`, and zeros elsewhere. Since
`0 <= E < b^(L+1)` and `H` has no digit below position `L + 2`, the digits of
`N` are those of `H` together with those of `E`. If `c_x >= 2`, then
`c_x x >= 2x > b`, so `h_x >= 1`. Also `h_x < c_x <= D* <= b/2`, so `h_x`
is a nonzero digit below every designated digit. That is a prohibited digit
of `n`, against Step 2. So every `c_x` is 0 or 1.

Step 5 (the error is zero). Let `X` be the set of designated digits with
`c_x = 1`. By Step 4, `H` has the digit `x` at `P_x` for each `x` in `X`, and
no other nonzero digit. The multiset condition says that each `x` in `X`
appears exactly once in `N`, and that no other nonzero digit appears. So the
digits of `E` are all 0, and `E = 0`.

Step 6 (the mandatory digit). If `z` is not in `X`, then `X` is a nonempty
set of item digits (Step 3 excluded the empty set), and
`E = p sum over X of a_i > 0`, against Step 5. So `z` is in `X`, and
`0 = E = p (sum over S of a_i - T)` with `S = {i : x_i in X}`. Then
`n = H = n_S`.

Corollary 13.4. GEN is NP-complete. This holds also for the instances with
`w(0) = 0`, strictly increasing weights and `W < b^(b/2)`.

Proof. NP-hardness follows from Theorem 13.3, because SUBSET-SUM is
NP-complete. For increasing weights, change the roles: `x_i = b - 3 - k + i`
for `i = 1, ..., k`, `z = b - 2`, and `w(b-1) = (b-1) b^(P_z) + 1`. The
prohibited digits are now `1, ..., b - 3 - k` and `b - 1`. Then
`w(y) = y + 1 < w(x_1) < ... < w(x_k) < w(z) < w(b-1)`, and the item weights
increase because the positions do. The proof of Theorem 13.3 needs only that
designated digits satisfy `w(x) == x (mod p)`, that prohibited digits satisfy
`w(y) == y + 1 (mod p)`, that all weights lie below `b^(P_z + 1)`, and that
the designated digits lie in `(b/2, b-2]`. All four still hold:
`w(b-1) - (b-1) = (b-1)(b^(P_z) - 1) + 1 == 1 (mod p)`. Finally
`P_z + 1 = D* - 1 < b/2`.

Corollary 13.5. Counting the solutions of GEN is #P-complete under
parsimonious reductions, also for increasing weights.

Proof. The counting problem is in #P by Proposition 13.2: the accepting
certificates are the solutions. Theorem 13.3 is parsimonious. #SUBSET-SUM is
#P-complete under parsimonious reductions. One route: #SAT is #P-complete
under parsimonious reductions (the Cook-Levin construction is parsimonious),
and so is #3SAT (the clause splitting with fresh variables determines the
fresh variables). The textbook reduction from 3SAT to SUBSET-SUM (Cormen,
Leiserson, Rivest and Stein, section 34.5.5) is parsimonious. For each
variable it has two numbers, of which exactly one is chosen, according to the
assignment. For each clause it has two slack numbers, 1 and 2, in the clause's
digit, with target 4 there. A clause with `t` true literals, `t` in
`{1, 2, 3}`, needs slack `4 - t`, which is `1 + 2`, `2` or `1`: in every case
exactly one choice. So each satisfying assignment gives exactly one subset.
All its numbers are positive.

The reduction uses `w(0) = 0`, the analog of `0^0 = 0`. I did not settle the
variant with `w(0) = 1` forced. There every zero costs 1, so the error depends
on the number of zeros, and Step 2 of Theorem 13.3 no longer isolates the prohibited
digits.

### 13.1.3 The gadgets that fail

The gadgets of the sketch in question 27 need two changes. Both are visible
in `python analysis/thy_reduction.py broken`, on the instance `a = (2, 3)`,
`T = 4`, which has no solution.

- Prohibited digits need a reason to be absent. If they get the weight `y`,
  they pay for themselves at position 0, and the table has 68 solutions. With
  the weight 0 they are wildcards: their count is free, and the table has 3
  solutions, for example `(15, 19, 19, 19, 19, 19, 19, 16, 4)`. The residue
  modulo `p` in Step 2 is what removes them. It needs a uniform bound on the
  number of digits, which Lemma 13.1(b) provides.
- The errors must be multiples of `p`. With errors `a_i` and `-T` the residue
  argument breaks, a prohibited low digit can absorb a nonzero error, and the
  table has 16 solutions such as `(16, 0, 17, 0, 0, 0, 0, 0, 1)`.

Repeated digits and carries are handled by placing all designated digits
above `b/2`: two copies of a digit always carry a nonzero small digit into the
next position, and small digits are prohibited (Step 4). A negative error
borrows through the gap at position `L + 1` and leaves the prohibited digit
`b - 1` there (Step 3). A missing mandatory digit leaves a positive error
(Step 6).

### 13.1.4 The check

`analysis/thy_reduction.py` builds the table of Theorem 13.3 and of
Corollary 13.4, and finds every solution with an exact search that uses only
Lemma 13.1(a), not the proof of Theorem 13.3. The search fixes the counts of
the heavy digits, tries every total of the light weights, and checks the
digits of the resulting number. On 300 random weight tables in bases 3 to 7
it agrees with plain enumeration of all numbers up to the length bound
(`selftest`).

| items `k` | `a_i` up to | base | longest possible solution | tables | with a solution | count = subset count |
|---:|---:|---:|---:|---:|---:|---|
| 1 to 3 | 4 | 18 to 24 | 8 to 12 digits | 1,476 | 948 | all |
| 4 | 2 | 30 | 14 digits | 414 (all `k <= 4`) | 334 | all |

Every target `T` from 0 to `sum a_i + 1` was tried, with both the plain and
the increasing tables. In every case the solutions are exactly the numbers
`n_S`, so the count is the number of subsets.

### 13.1.5 Weights that are powers of the digit

Now let `w(x) = x^(e(x))` with `w(0) = 0` or 1, and the exponents given in
unary or in binary.

Proposition 13.6. With exponents in unary, the problem is in NP. If all
exponents are at most a constant `K`, it is in P.

Proof. Here `W <= (b-1)^K` with `K = max e(x)`, which is at most the input
size. By Lemma 13.1(a) a solution has `O(K log b)` digits, and the check is
polynomial. If `K` is a constant and `b > K + 2`, Lemma 13.1(b) with `M = K`
gives `D <= K + 1`, so trying all `b^(K+1)` numbers takes polynomial time.
Bases `b <= K + 2` are finitely many.

With exponents in binary, a solution can have about `e log_b x` digits, which
is exponential in the input size. The problem is in NEXP. I do not know
whether it is in NP. A certificate would have to let the verifier find the
digit histogram of `sum c_x x^(e(x))` for exponents with polynomially many
bits, and no polynomial method for the middle digits of huge powers is known.

NP-hardness is open in both versions. The reduction of Theorem 13.3 needs about
`k` digit values whose weights have a prescribed base-`b` expansion: one
digit at a chosen position plus a low part that the solution can control. For
a pure power this means that `x^(e-1)` equals `b^P` exactly, or nearly.
Exactly: then `x` and `b` are powers of one integer (as in the proof of
Proposition 2.2), and a base has fewer than `log2 b` such digits (the count
of Proposition 8.5). But `k` items need a base of size `2^(Omega(k))`, which
is not polynomial in unary. Nearly: the
difference `x^e - x b^P` is itself a long number whose digits nobody controls,
and each of them must match the multiset. So the hardness of the power
variants is a question about the digits of powers, the same arithmetic that
section 8.2 meets.

### 13.1.6 What this means next to section 8.1

Section 8.1 shows that `L_m` is in NP and is a tally language, so it is not
NP-hard unless P = NP (Berman 1978; Mahaney 1982 for sparse sets).
Corollary 13.4 shows that the same question with the weights left free is
NP-complete. The two problems differ in one point: `L_m` fixes the weights,
and that leaves one instance per base.

- Every algorithm that treats the weights as an oracle is subject to
  Corollary 13.4. This includes the prefix-pruned tree of chapter 6, which needs
  only increasing weights, the splits and joins of sections 6.3 and 10.4, and
  the near-solution search of chapter 11. On the instances of Corollary 13.4
  the weights are increasing and below `b^(b/2)`, the same size regime as
  `x^x`, and the input has `O(b^2 log b)` bits. So no algorithm that is
  correct for all such tables runs in time polynomial in `b`, unless P = NP.
- A fast algorithm for `L_m` itself is not excluded. It would have to use the
  arithmetic of `x^x`: congruences, the leading digits of powers, or other
  facts that arbitrary weights do not share. Proposition 10.2 and the local
  obstructions of chapter 11 are of this kind, but they only give constant
  factors so far.
- Section 8.1 can be sharpened. Book (1974) proved that NP contains a tally
  set outside P exactly when NE != E. So a proof that `L_m` is not in P would
  prove NE != E, which is stronger than P != NP.
- The counting function `b -> N_m(b)` is in #P. It is not #P-complete under
  parsimonious reductions unless P = NP: such a reduction from #SAT would map
  satisfiable formulas to bases with a solution, a many-one reduction from SAT
  to a tally set. For GEN, counting is #P-complete (Corollary 13.5).
- The hard instances are unlike the real ones. Their solutions have at most
  `b/2` digits, and their number is the number of subsets with sum `T`, which
  can be exponential in `b`. Real solutions have about `b - 1` digits and
  follow the model of chapter 5. Whether GEN stays NP-hard on tables whose
  solutions must be long is open.

## 13.2 A Poisson theorem in the model

### 13.2.1 The coupled model

The model of chapter 5 assigns a probability to each multiset separately. To
state a joint law for both conventions, the model must say how the events
depend on each other. The coupled model does this with one random number per
upper part.

Fix a base `b`. Split a digit multiset `c` into its counts `c_0`, `c_1` of
zeros and ones and its upper part `u = (c_2, ..., c_(b-1))`. Let `|u|` be
the number of digits in `u`, and `d = c_0 + c_1 + |u|` the length. Put

    V(u) = sum over x >= 2 of c_x x^x,    D_u = number of digits of V(u).

Then `F_m(c) = V(u) + c_1 + m c_0`. Let `j_m(c) = c_1 + m c_0`.

Definition (coupled model). For each upper part `u`, let `Y_u` be a random
integer with `D_u` digits. The `Y_u` are independent.

- Basic version: `Y_u` is uniform on `[b^(D_u - 1), b^(D_u))`.
- Refined version: `Y_u` is uniform on the numbers of that interval that are
  `== V(u) (mod b-1)`. Each such residue class has exactly `b^(D_u - 1)`
  members.

The multiset `c` is a model solution under convention `m` if the digits of
`Y_u + j_m(c)` form `c`.

So the model replaces the number `V(u)` by a random number of the same
length and, in the refined version, the same residue modulo `b - 1`, and keeps
the exact additions of the small digits. For one multiset, the probability of
a solution is the chapter 5 value up to a relative error of order `d/b^(d-1)`
from the boundary of the interval. The refined version builds in Proposition
1.5 of the library: `Y_u + j_m(c) == F_m(c) (mod b-1)`.

Three dependencies are now exact:

- Twins. Under `m = 0`, if `Y_u + c_1` has the multiset `c` and ends in 0, then
  `Y_u + c_1 + 1` has the multiset with one 0 replaced by a 1.
- Shared solutions. If `c_0 = 0`, then `j_0(c) = j_1(c)`, and `c` is a solution
  under both conventions or under neither.
- The residue. All completions of one upper part share `Y_u`, and in the
  refined version they share its residue.

Index set. Fix a minimal length `ell >= 6`. An index `alpha` is a multiset `c`
with `ell <= d <= b` and `|u| >= 2`, together with a convention `m`, where the
two conventions are one index when `c_0 = 0`. So there are three types:
shared (`c_0 = 0`), type 0 and type 1 (`c_0 >= 1`, convention 0 or 1). Let
`X_alpha` be the indicator of a model solution, `p_alpha = E X_alpha`, and

    N_0 = sum over shared and type 0,   N_1 = sum over shared and type 1,
    lambda_s, lambda_0, lambda_1 = sum of p_alpha over each type.

The condition `|u| >= 2` leaves out strings with at most one digit above 1,
such as `(x, 0, ..., 0, 1)`. These are the self-paying families of chapter 2.
In the model they have total mass below `b d (2/b)^(d-1)`.

The cluster of `alpha` is the set of indices with the same upper part. Indices
in different clusters are independent, because they depend on different
`Y_u`.

### 13.2.2 Twins are the only coupling

Lemma 13.7. Let `alpha` and `beta` be distinct indices in one cluster, and
suppose that both are solutions. Then both are shared or type 0, the string of
one ends in 0, and the string of the other is that string plus 1. Conversely,
if a shared or type 0 index `alpha` is a solution whose string ends in 0 or 1,
its twin is a solution too.

Proof. Write `s` for the string `Y_u + j_alpha` and `s' = Y_u + j_beta =
s + delta` with `delta = j_beta - j_alpha`. Treat a shared index as convention
0. Both strings have the upper part `u`. Since `j <= d <= b` for every index,
`|delta| <= b`.

Equal lengths. Suppose `s'` has more digits than `s`. Then
`s >= b^d - b`, so the positions 2 to `d - 1` of `s` hold `b - 1`, that is at
least 4 copies, while `s' < b^d + b^2` has zeros there and at most 2 copies of
`b - 1`. The upper parts differ, which is impossible. If `s'` has fewer
digits, swap the roles. So `s` and `s'` have the same length, and
`Delta_0 + Delta_1 = 0`, where `Delta_0` and `Delta_1` are the changes in the
numbers of zeros and ones.

Digit sums. The upper parts agree, so the digit sum changes by `Delta_1`.
Adding a positive `delta` with `k` carries changes the digit sum by
`ds(delta) - k (b - 1)`, where `ds` is the digit sum, and `ds(delta) <= delta`
with equality only for `delta < b`.

- Both convention 0: `delta = Delta_1`. If `delta > 0`, then
  `delta = ds(delta) - k (b-1)` forces `delta < b` and `k = 0`. If
  `delta < 0`, apply this to `s = s' + |delta|`. So no carry occurs, only the
  last digit changes, and it changes from 0 to 1 or back, because the upper
  parts agree. So `delta = 1` or `-1` and the pair is a twin pair.
- `alpha` convention 0, `beta` type 1: `delta = Delta_1 + c'_0`, where
  `c'_0 >= 1` is the number of zeros of `s'`. If `delta > 0`, then
  `c'_0 = delta - ds(delta) + k (b-1)`, a multiple of `b - 1`, because
  `delta == ds(delta) (mod b-1)`. If `delta < 0`, the same computation for
  `s = s' + |delta|` gives `c'_0 <= 0`. So `c'_0 >= b - 1`, and `s'` has at
  most `d - (b-1) <= 1` nonzero digits. Then `|u| <= 1`, which is excluded.
- `alpha` type 1, `beta` convention 0: the same with the roles swapped.
- Both type 1: `delta = Delta_1 + Delta_0 = 0`, so `alpha = beta`.

For the converse: if `s` ends in 0, then `s + 1` has the multiset with one 0
replaced by a 1, the same upper part and length, and `j_0` grows by 1. So
`Y_u + j_0` of that multiset is `s + 1`. If `s` ends in 1, the same holds for
`s - 1`.

### 13.2.3 The theorem

Theorem 13.8 (Poisson approximation in the coupled model). Let `Z_s`, `Z_0`,
`Z_1` be independent Poisson variables with means `lambda_s`, `lambda_0`,
`lambda_1`. In the basic and in the refined coupled model,

    d_TV( (N_0, N_1), (Z_s + Z_0, Z_s + Z_1) ) <= 2 b_1 + b_2,

where `d_TV` is the supremum of `|P(A) - Q(A)|` over events,
`b_1 = sum over clusters of sigma_u^2`, `sigma_u` is the sum of `p_alpha` over
the cluster, and `b_2 = 2 E[T]`, where `T` is the number of shared or type 0
model solutions whose string ends in 0.

Proof. It suffices to compare the whole family `(X_alpha)` with a family
`(Z_alpha)` of independent Poisson variables with means `p_alpha`, because
`(N_0, N_1)` is a function of the family, and summing the `Z_alpha` by type
gives `Z_s`, `Z_0`, `Z_1`. The clusters are independent in both families, and
total variation distance is subadditive over independent components. So it
suffices to show, for one cluster with indicator vector `X` and
`sigma = sum p_alpha`, that

    d_TV(X, Z) <= E[K (K - 1)] + 2 sigma^2,          K = sum over the cluster of X_alpha,

and then to sum over clusters, where `sum E[K(K-1)]` is the expected number of
ordered pairs of distinct solutions in one cluster. By Lemma 13.7 these are the
twin pairs, each counted twice, so this sum is `2 E[T]`.

Let `B` be a vector of independent Bernoulli variables with means
`p_alpha`. Le Cam's inequality gives `d_TV(B, Z) <= sum p_alpha^2 <=
sigma^2`. For `X` against `B`, write `d_TV = (1/2) sum over 0/1 vectors v of
|P(X = v) - P(B = v)|` and split by the weight of `v`.

- Weight at least 2: the sum is at most `P(K >= 2) + P(|B| >= 2)`, and
  `P(|B| >= 2) <= sigma^2 / 2`.
- `v` the unit vector of `alpha`: `P(X = v) = p_alpha - P(X_alpha = 1, K >= 2)`
  and `p_alpha (1 - sigma) <= P(B = v) <= p_alpha`. Summed over `alpha`, the
  differences are at most `E[K 1(K >= 2)] + sigma^2`.
- `v = 0`: `P(X = 0) = 1 - sigma + E[(K - 1)^+]`, and
  `1 - sigma <= P(B = 0) <= 1 - sigma + sigma^2 / 2`. The difference is at most
  `E[(K-1)^+] + sigma^2 / 2`.

With `P(K >= 2) <= E[K(K-1)]/2`, `E[K 1(K >= 2)] <= E[K(K-1)]` and
`E[(K-1)^+] <= E[K(K-1)]/2`, the total is at most
`2 E[K(K-1)] + 2 sigma^2`, so `d_TV(X, B) <= E[K(K-1)] + sigma^2`. Adding
`d_TV(B, Z) <= sigma^2` gives the claim.

### 13.2.4 The error terms

Lemma 13.9. In both versions, for every cluster,

    sigma_u <= 4 b (b + 1) ell! / b^ell.

So `b_1 <= 4 b (b+1) (ell! / b^ell) (lambda_s + lambda_0 + lambda_1)`. For
`ell = ceil(b/2)` this decays like `(2e)^(-b/2)` up to a power of `b`.

Proof. For each convention `m` and each `j` from 0 to `b`, the indices with
`j_m = j` are solutions only if `Y_u + j` has the upper part `u`, and at most
one of them is a solution at a time. So `sigma_u` is at most the sum over
these `2 (b+1)` pairs of `P(Y_u + j has upper part u)`. In both versions each
value of `Y_u` has probability at most `1 / b^(D-1)`, with `D = D_u`. The
number `Y_u + j` has `D` or `D + 1` digits. With `D + 1` digits it lies in
`[b^D, b^D + b]` and has at most one digit above 1, which `|u| >= 2`
excludes. Strings of length `D` with upper part `u` number at most
`D! 2^z / z! <= 2 D!`, where `z = D - |u|`. So each probability is at most
`2 D! / b^(D-1)`. Indices have `ell <= D <= b`, and `D! / b^D` decreases in
`D` there.

Lemma 13.10. In the basic model with `ell >= b/2` and `b >= 12`,
`E[T] <= 7.1 / b`. In the refined model the same holds with `7.1 kappa / b`
under the following assumption.

Assumption R (residues spread). For every `d` and every residue `r`, among
uniform strings `t` of `d - 1` digits whose `V` has `d` digits, the share with
`sum c_x (x^x - x) == r (mod b-1)` is at most `kappa / (b - 1)`.

Proof. A model solution counted by `T` is a string `t` of length `d` that ends
in 0. In the basic model the probability that `Y_u + c_1 = t` is at most the
probability that a uniform `d`-digit string equals `t`, and it is 0 unless
`V(u)` has `d` digits. (A string with `d` digits reached from
`D_u = d - 1` lies in `[b^(d-1), b^(d-1) + b]` and has `|u| <= 1`.) The last
digit 0 adds nothing to `V`. So

    E[T] <= sum over d of (1/b) P(G_d),

where `G_d` is the event that the top `d - 1` digits of a uniform string have
`V` with `d` digits. In the refined model each value has probability at most
`1 / b^(d-2)`, that is `b - 1` times more, but only strings in one residue
class count. Under Assumption R this gives the factor `kappa`.

On `G_d` every digit `x` has `x^x < b^d`. Write `d = b - j`. For
`x = b - j + i <= b`, `ln x >= ln b - (b - x)/x`, so
`x ln x >= (b - j + i) ln b - (j - i)`, which is at least `d ln b` once
`i >= j / (1 + ln b)`. So all digits are below `b - theta j + 1` with
`theta = ln b / (1 + ln b) >= 0.71`, and

    P(G_(b-j)) <= (1 - (theta j - 1)/b)^(b-j-2) <= exp(-0.3 (theta j - 1)),

using `(b - j - 2)/b >= 0.3` for `j <= b/2` and `b >= 12`. Summing over
`j >= 0` gives at most `e^0.3 / (1 - e^(-0.213)) <= 7.1`.

Corollary 13.11. Let `ell = ceil(b/2)` and `b >= 12`. In the basic coupled model,

    d_TV( (N_0, N_1), (Z_s + Z_0, Z_s + Z_1) ) <= 14.2 / b + 16 b^2 (b+1) ell! / b^ell.

In the refined model the same holds with `14.2 kappa / b` and an extra factor
`b - 1` in the last term, under Assumption R. In either case the joint law of
`(N_0, N_1)` is within `O(1/b)` of a bivariate Poisson law.

Proof. Combine Theorem 13.8 with Lemmas 13.9 and 13.10. It remains to bound
`lambda = lambda_s + lambda_0 + lambda_1`. In the basic model,
`p_alpha` is at most the probability that a uniform `d`-digit string has the
multiset of `alpha` (the case `D_u = d - 1` is excluded by `|u| >= 2`, as in
Lemma 13.9). Summing over the multisets of one length and over the two
conventions gives at most 2 per length, so `lambda <= 2b`. In the refined
model each probability is at most `b - 1` times larger, so
`lambda <= 2 b (b-1)`.

The bound `lambda <= 2b` is crude. Section 5.2 computes that `lambda` tends to
about 1.6 in even bases and 2.4 in odd ones, and the table in section 13.2.5
agrees.

Status of the pieces:

- Theorem 13.8, Lemma 13.7, Lemma 13.9, the basic case of Lemma 13.10 and the basic
  case of Corollary 13.11 are proven.
- The refined case rests on Assumption R. It is a statement about the
  residues of `x^x` modulo the odd prime powers in `b - 1`, not about the
  model's randomness, and it is the same assumption that section 5.3 uses to
  get the factor 1 for odd primes. The prime 2 forces `kappa >= 2` in odd
  bases, and a proof of R with some constant `kappa` is the gap.

The constant 14.2 is crude. `analysis/thy_poisson.py` computes `b_2` in the
refined model by sampling, with every partner checked by brute force over all
shifts `|delta| <= 2b + 2`. It finds no partner other than twins, as
Lemma 13.7 says, and `b_2 b / lambda` is 1.2 to 1.4 in even bases and 1.6 to
2.2 in odd bases from 10 to 41. At base 30, `b_2 = 0.07`. Summed over bases
10 to 41, the model expects `sum E[T] = 2.7` twin pairs. The data have 5
solutions under `0^0 = 0` that end in 0, each with its twin.

### 13.2.5 The joint law and the correlation

Under Corollary 13.11, `(N_0, N_1)` is approximately a bivariate Poisson pair
`(Z_s + Z_0, Z_s + Z_1)`. Within one base its correlation is

    rho(b) = lambda_s / sqrt( (lambda_s + lambda_0) (lambda_s + lambda_1) ).

Large-base limit. A model solution has `d = b - j` digits with `j` bounded,
and its zeros are a Binomial(`d - 1`, `1/b`) count, nearly independent of the
large digits that decide the length. So it is zero-free with probability
tending to `e^(-1)`. With the refined factors of section 5.3:

| | `lambda_s` | `lambda_0` | `lambda_1` | `E N_0` | `E N_1` | `rho` |
|---|---:|---:|---:|---:|---:|---:|
| even base | `e^-1` = 0.368 | `1 - e^-1` = 0.632 | 0.632 | 1 | 1 | `e^-1` = 0.368 |
| odd base | `2 e^-1` = 0.736 | `2 - 2e^-1` = 1.264 | `1 + e^-2 - 2e^-1` = 0.399 | 2 | 1.135 | 0.488 |

In odd bases under `0^0 = 1`, the parity rule of section 1.6 requires an even
number of zeros. Zero-free strings always meet it, so they keep the factor 2,
and the shared share rises. These limits use the large-base computation of
section 5.2 and the factor 1 for odd primes of section 5.3. Both are model
computations, not theorems.

Finite bases. `python analysis/thy_poisson.py means 10 41 20000` samples the
refined coupled model for lengths `b - 14` to `b`:

| base | `lambda_s` | `lambda_0` | `lambda_1` | `E N_0` | `E N_1` | `rho(b)` | `b_2` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 0.671 | 0.693 | 0.659 | 1.364 | 1.330 | 0.498 | 0.334 |
| 11 | 1.134 | 1.248 | 0.300 | 2.382 | 1.434 | 0.614 | 0.449 |
| 20 | 0.454 | 0.644 | 0.647 | 1.098 | 1.102 | 0.413 | 0.110 |
| 21 | 0.906 | 1.302 | 0.379 | 2.208 | 1.285 | 0.538 | 0.214 |
| 30 | 0.417 | 0.623 | 0.626 | 1.040 | 1.043 | 0.400 | 0.071 |
| 31 | 0.826 | 1.278 | 0.366 | 2.103 | 1.191 | 0.522 | 0.136 |
| 40 | 0.400 | 0.614 | 0.636 | 1.014 | 1.036 | 0.391 | 0.051 |
| 41 | 0.802 | 1.273 | 0.372 | 2.075 | 1.174 | 0.514 | 0.102 |
| 60 | 0.381 | 0.610 | 0.609 | 0.991 | 0.990 | 0.384 | 0.033 |
| 100 | 0.407 | 0.615 | 0.628 | 1.023 | 1.036 | 0.396 | 0.021 |
| 150 | 0.389 | 0.598 | 0.600 | 0.987 | 0.989 | 0.394 | 0.014 |

(Bases 60 to 150 with 4,000 samples per length.)

The finite-base values approach the limits slowly, because the zero count of a
`(b-1)`-digit string is Binomial(`b - 2`, `1/b`), zero-free with probability
`(1 - 1/b)^(b-2)`, which is 0.40 at base 20.

The pooled correlation. Section 4.3 reports 0.56 for the correlation of
`n0` and `n1` over bases 10 to 41. That is a correlation across bases, so it
has two sources: the shared solutions within each base, and the parity of the
base, which raises the means of both counts in odd bases (2.1 and 1.2 against
1.04 and 1.04). `python analysis/thy_poisson.py corr` draws the 32 pairs from
the bivariate Poisson laws with each base's own means and computes the sample
correlation, 200,000 times:

| | value |
|---|---:|
| model totals, bases 10-41: `lambda_s`, `lambda_0`, `lambda_1` | 21.9, 31.1, 16.3 |
| model totals: `E N_0`, `E N_1` | 53.0, 38.2 |
| observed totals: `N_0`, `N_1`, shared | 66, 56, 35 |
| model sample correlation, mean and median | 0.470, 0.482 |
| model sample correlation, 5% to 95% | 0.19 to 0.71 |
| observed | 0.563 |
| model probability of a correlation of at least 0.563 | 0.30 |

So the model predicts about 0.47 and the observed 0.56 is an ordinary draw.
The prediction splits into a within-base part (about 0.40 in even bases and
0.52 in odd bases at these sizes) and the parity part, which lifts the pooled
value. The model share of shared solutions among those under `0^0 = 1` is
`21.9 / 38.2 = 0.57`. The data have `35 / 56 = 0.63`.

The observed correlation of the solutions with at least `b - 6` digits, the
range where the model applies, is 0.69. Small bases contain the algebraic
families of chapter 2, which the model does not describe.

### 13.2.6 What remains open

- Assumption R. A proof needs the residues of `x^x` modulo the odd prime
  powers dividing `b - 1` to spread over the classes, uniformly over the
  strings whose sum has the right length.
- The limits of the means. Section 5.2 computes them with Poisson digit
  counts. A proof would turn that computation into a theorem about the model.
- The real weights. Theorem 13.8 is about the model. Section 11.1 found that
  the real counts behave like Poisson draws with each base's own mean. Whether
  this can be proven for `x^x` is the question of sections 8.5 and 6.4.
