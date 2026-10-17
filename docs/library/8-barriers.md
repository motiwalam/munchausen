# 8. What can be solved, and why the rest is hard

Chapter 7 lists the open problems. This chapter settles some of them, proves
partial results for others, and explains for each remaining one which
well-known barrier stands in the way.

## 8.1 Fast algorithms and P versus NP

Let `L_m` be the set of strings `1^b` (the base written in unary) such that
base `b` has a nontrivial solution under convention `m`.

Proposition 8.1. `L_m` is in NP.

Proof. A solution has at most `b` digits, each below `b`, so it can be written
with `O(b log b)` bits. Checking it means computing `n` and `F(n)`. Each weight
`x^x` has at most `b log2 b` bits, so the check takes time polynomial in `b`.

Corollary 8.2. If no algorithm decides `L_m` in time polynomial in `b`, then
P is not equal to NP.

So a proof that Munchausen numbers cannot be found in polynomial time would
also settle the P versus NP problem. The usual way to give evidence of
hardness does not work either. `L_m` is a tally language: it has at most one
string of each length. Berman (1978) showed that if a tally language is
NP-complete, then P = NP. Mahaney (1982) extended this to all sparse
languages. So, unless P = NP, no reduction from an NP-complete problem to
`L_m` exists.

In short:

- an unconditional lower bound would prove P != NP;
- an NP-hardness proof would prove P = NP.

Neither direction is available. So the question "is there a polynomial-time
search?" is out of reach of current methods. Chapter 6 gives the heuristic
reasons to expect that the answer is no.

## 8.2 Short solutions: a partial finiteness theorem

Chapter 3 conjectures that under `0^0 = 1`, each length `k >= 3` has only
finitely many solutions in all bases together. This section proves the
conjecture for a large part of the problem and shows what blocks the rest.

Theorem 8.3 (leading digit). Fix `k >= 2` and `k-1` digits below a bound `B`.
Consider the `k`-digit strings whose leading digit is `x` and whose other
digits are the fixed ones. Suppose that `x^(x-1)` is a perfect `(k-1)`-th
power, for example because `k-1` divides `x-1`. Then, for `x` larger than an
explicit bound that depends on `B` and `k`:

- under `0^0 = 0`, the only solutions are `(x, 0, ..., 0, 0)` and
  `(x, 0, ..., 0, 1)`, the self-paying digit of section 2.2;
- under `0^0 = 1`, the only solutions are `(x, 1)` with `k = 2`, in base
  `x^(x-1)`. For `k >= 3` there are none.

Proof. Write `x^(x-1) = Z^(k-1)`, let `Q(b)` be the value of the lower `k-1`
digits and `C` the sum of their weights. The equation is
`x b^(k-1) + Q(b) - C = x Z^(k-1)`, with `0 <= Q(b) < 2B b^(k-2)`.

- If `b >= Z + 1`, the left side is at least
  `x Z^(k-1) + x (k-1) Z^(k-2) - C`, which exceeds the right side once
  `x (k-1) Z^(k-2) > C`.
- If `b <= Z - 1`, the left side is at most
  `x Z^(k-1) - (Z-1)^(k-2) (x (k-1) - 2B)`, which is smaller than the right
  side once `x (k-1) > 2B`.

So `b = Z` and `Q(Z) = C`. If a lower digit at a position `i >= 1` is not 0,
then `Q(Z) >= Z > C` for large `x`. So those digits are all 0, and the last
digit `e` satisfies `e = (k-2) w(0) + w(e)`. Under `0^0 = 0` this means
`e^e = e`, so `e` is 0 or 1. Under `0^0 = 1` it means `e = k - 2 + w(e)`.
Since `w(e) >= e` for every digit, that forces `k = 2` and `e = 1`.

For 3 digits the same idea works when the variable digit is not the leading
one. Completing the square turns `p b^2 + q b + r = F` into
`(2pb + q)^2 = 4 p F + q^2 - 4 p r`. If the dominant term `4 p x^x` is a
perfect square, the right side is a square plus a term of size at most about
`x^2`. Two squares that close must be equal, which bounds `x`.

Call the case where the dominant term is a perfect power the square class. For
3 digits it is: `x` leading and `x` odd or a square; or `x` not leading and
`p x^x` a square, for example `p` a square and `x` even.

Corollary 8.4 (complete result for one large digit). Under `0^0 = 1`, consider
the 3-digit solutions in which two digits are at most 20 and the third digit
`x` lies in its square class. The bound of the theorem is `x <= 35`
(`analysis/square_class_bound.py`). The scan in `analysis/patterns.py` covers
`x` up to 2500, so it finds all of them: they are the known solutions of
section 3.2.

The rest of the problem. Outside the square class, the equation asks whether
`4 p x^x + R(x)` is a perfect square while `4 p x^x` is not. Writing
`4 p x^x = N Y^2` with `N` square-free, this is the Pell-type equation
`r^2 - N Y^2 = R` with the extra condition that `Y` equals a prescribed number
like `x^((x-1)/2)`. For each single `x` this is decidable. For all `x` at once
it asks whether an exponentially growing sequence ever lands on the solution set
of a Pell equation. That solution set changes with `x`. For longer numbers it asks
whether `x^((x-1)/(k-1))` comes within about `B/x` of an integer.

Questions of this kind are far from current methods. For comparison, even for
the single sequence `(3/2)^n` it is not known whether the fractional parts are
dense in `[0, 1]`. That is a simpler-looking question of the same type: how
close does a growing power come to an integer? I found no published result that handles equations
in which the base and the exponent of `x^x` vary together.

So a proof of finiteness for all short solutions under `0^0 = 1` would need
new methods for exponential Diophantine equations. The numerical evidence is
strong: outside the square class, the scan with `x` up to 2500 (bases up to
about `10^4000`) also finds only the known solutions.

## 8.3 Self-paying digits never sit side by side

Proposition 8.5. In every base, two self-paying digits `r^s` and `r^u` with
`s < u` sit at positions `k_s` and `k_u` with `k_u > r k_s >= 2 k_s`. So a base
has fewer than `log2 b` self-paying digits, and no two of them are adjacent.

Proof. By Proposition 2.2, `k_u / k_s = u (r^u - 1) / (s (r^s - 1))`. With
`u >= s + 1` this is at least `(r^(s+1) - 1) / (r^s - 1)`, which is larger than
`r`. The count is below `t = log_r b <= log2 b`.

`analysis/` checks this for all 35 pairs of self-paying digits in bases up to
100,000.

Corollaries:

- Under `0^0 = 1`, every placement with zero balance is a self-paying digit or
  a final 1, because a zero weighs 1. A solution made only of such placements
  needs a self-paying digit at every position above 0. By Proposition 8.5 that
  is only possible with 2 digits. So the only such solutions under `0^0 = 1` are
  `(a, 1)` in base `a^(a-1)`.
- Under `0^0 = 0`, Corollary 2.4 gives at least `2^(C+1) - 2` solutions, and
  `C < log2 b`. So the self-paying digits multiply the number of cores by less
  than `2b`. Large counts can only come from many cores, or from bases with
  many self-paying digits, as in Proposition 4.2.

## 8.4 Self-paying digits under `0^0 = 1`: near-solutions

Under `0^0 = 1`, replacing a self-paying digit by 0 changes `n` by `-a b^k` and
`F(n)` by `-a^a + 1`. So it does not give a solution. It gives a near-solution
with `F(n) = n + 1`.

Here a near-solution is a digit string of a fixed length `L`, leading zeros
allowed, where every zero, including the leading ones, weighs 1.

Proposition 8.6. Under `0^0 = 1`, the solutions of length `L` that contain `j`
self-paying digits correspond exactly to pairs made of:

- a string `n` of length `L` with `F(n) = n + j` (a near-solution with defect
  `j`), and
- a choice of `j` self-paying positions where `n` has the digit 0, such that
  the result does not start with 0.

Proof. Each self-paying digit placed on a 0 lowers the defect `F(n) - n` by
exactly 1.

So whether `N_1(b)` can be large depends on near-solutions with small defects,
and those are coincidences of the same kind as solutions. Base 64 shows one:
`(16,0,0,0,0,0,1,0,0,4,8)` contains the self-paying digits 16 and 4, and
replacing them by zeros leaves the 11-digit string `(0,0,0,0,0,0,1,0,0,0,8)`.
Its weight is `9 + 1 + 8^8 = 16777226`, two more than its value
`64^4 + 8 = 16777224`, so it is a near-solution with defect 2. In the model,
near-solutions are coincidences at about the same rate as solutions. So bases
with many self-paying digits are expected to have several solutions under
`0^0 = 1` from time to time. A construction like
Proposition 4.2 would need near-solutions with every small defect in one base,
and none is known. Whether `N_1(b)` is bounded therefore stays open, for the same
reason as in section 8.2: each step needs an exact coincidence between powers.

## 8.5 Bases without solutions

Showing that one base has no solution is a finite computation, and the search
does it. Bases 19, 27 and 35 are the examples up to 41. Base 43, the next base
`== 3 (mod 8)`, has a solution, so that pattern from section 4.5 was chance.

Showing that infinitely many bases have no solution needs an argument that works
for infinitely many bases at once. The tools of this library cannot give one:

- Congruences only remove a fixed fraction of the candidates. For a modulus
  `q`, about `1/q` of all numbers satisfy `n == F(n) (mod q)`, and almost all of
  them are not solutions.
- The constructions of chapter 2 only show that bases have solutions, never
  that they lack them.
- In the model, each base is empty with probability about 15%, independently of
  the others. A proof that infinitely many are empty would have to control
  these chance events in infinitely many bases. That is a statement of the same
  kind as the finiteness questions of section 8.2, about the absence of
  coincidences between powers, and no method for it is known.

The opposite statement, "every large base has a solution", is as far out
of reach, and the model says it is false.

## 8.6 Solutions with `b` digits under `0^0 = 1`

The model expects a `b`-digit solution in about 8% of large bases. If the model
is right, the conjecture is false, and a counterexample is a matter of
searching far enough. A proof of the conjecture would have to show that a whole
family of coincidences never happens, which runs into the barrier of section
8.5.

The search handles `b`-digit numbers alone (option `--min-digits`) at about a
quarter of the cost of a full base. Base 42 has no 42-digit solution under
either convention (29 minutes). Base 43, searched in full, also has none.
Searches of bases 44 to 46 are running.

## 8.7 Status

| problem | status |
|---|---|
| fast exact search | equivalent in difficulty to P vs NP; neither a lower bound nor NP-hardness can be shown without settling it (8.1) |
| finitely many short solutions under `0^0 = 1` | proven in the square classes and when one digit is large (8.2); the rest is a family of Pell-type equations with prescribed coordinates |
| lengths without solutions | same barrier as the finiteness question; verified up to base 100,000 for 9 digits and 10,000 for the others |
| is `N_1(b)` bounded | open; reduces to near-solutions with small defects (8.4) |
| `N_0(b)` unbounded | proven (Proposition 4.2) |
| infinitely many empty bases | open; no uniform method can exclude coincidences (8.5) |
| empty bases `== 3 (mod 8)` | resolved: base 43 has a solution |
| `b`-digit solutions under `0^0 = 1` | open; none in bases 3 to 43 (8.6) |
| excess of `(b-1)`-digit solutions | weak evidence in fresh data (probability 0.10); no mechanism found (5.5) |
