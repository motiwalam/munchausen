# Dynamics, two-digit bases, coverings and constructions

This draft answers questions 20, 13, 16, 14, 15 and 30 of `questions.md`.
Each statement carries one of three marks:

- proven: the proof is here;
- computed: an exhaustive computation, with its range;
- heuristic: a model or a conjecture, with its evidence.

Notation follows chapter 1. `w(x) = x^x` for `x >= 1`, `w(0) = m`, and
`g(c) = w(c) - c`.

## Summary

| question | answer | status |
|---|---|---|
| 20, cycle census | bases 3 to 17, both conventions. The only invariant residue is `n mod 2` in odd bases under `0^0 = 0`. A class-lumped random mapping predicts the cycle counts within 10% per group. The 2-cycle pattern of the lead does not persist: bases 13 and 15 have none, base 16 has one. | proven (invariant), computed (census), heuristic (model) |
| 13, two 2-digit solutions | only base 3 under `0^0 = 1`. Under `0^0 = 0` only base 3 and the twin bases `a^(a-1)`. | proven (Theorem 13.1) |
| 16, cores in self-paying bases | infinitely many 2-digit cores lie in self-paying bases: the swaps `(a, a^a)`. Apart from swaps, only `(1,3)` in base 25 for `a <= 200`, `c <= 3000`. Finiteness of the rest follows from abc in a large range. | proven (16.1, 16.2), computed, conditional (16.3) |
| 14, coverings | coverings beyond parity exist and are common. The cause is the 3-adic rule `x^x - x == 2 (mod 27)` for `x == 2 (mod 6)`. About 8% of all prefixes make the last digit hopeless. | proven (Lemma 14.2, Theorem 14.3), computed |
| 15, power identities | a chain-and-cycle construction covers the base-64 example. Bases `r^t` with `r <= 40`, `t <= 300` get at most 2 such solutions. No base with 6 found. | proven (Theorem 15.1), computed |
| 30, several bases | under `0^0 = 0` the number of bases is unbounded; `2^2048 + 1` has exactly 26. Under `0^0 = 1` at most two 2-digit bases, and no known integer has a third base. | proven (30.1, 30.2), computed |

## 20. Cycles of `n -> F(n)`

### 20.1 Setting

Proposition 20.1 (proven). Let `M_b` be the set of digit multisets with 1 to
`b` digits and at least one nonzero digit. The map `c -> multiset of S(c)`,
with `S(c)` the sum of the weights, sends `M_b` into itself. Its cycles
correspond one to one to the cycles of `n -> F(n)` on the integers `n >= 1`.

Proof. A multiset with `d <= b` digits has `S(c) <= b (b-1)^(b-1) < b^b`.
So `S(c)` has at most `b` digits. It has a nonzero digit because
`S(c) >= 1`. `F` depends only on the multiset, so a cycle of integers
gives a cycle of multisets of the same length. Two members of an integer
cycle with the same multiset have the same image, and a cycle is a
bijection on its members, so they are equal. The converse maps a multiset
cycle to the integers `S(c)`.

`|M_b| = C(2b, b) - 1`. A multiset of size at most `b` is a multiset of size
`b` over `0..b`. The sorted sequence `x_1 <= ... <= x_b` gives the subset
`y_i = x_i + i - 1` of `[0, 2b)`, which the combinatorial number system
ranks. `fast/src/bin/dyn_cycles.rs` walks the map with 2 bits of state per
multiset. Each multiset is entered once. Base 16 takes 165 s, base 17 takes
670 s per convention. Base 18 needs about 45 minutes per convention, so I
stopped at 17. Bases 3 to 9 agree with `analysis/questioner/cyc.py`. The
fixed points agree with the solution counts of chapter 4 plus the trivial
solution 1.

### 20.2 The census (computed)

Cycles of each length, the trivial fixed point 1 included
(`analysis/data/dyn_cycles.txt`):

| base | `0^0 = 0` | `0^0 = 1` |
|---:|---|---|
| 3 | 1:3, 2:1 | 1:3, 2:1 |
| 4 | 1:4 | 1:3, 2:1 |
| 5 | 1:3, 2:1, 4:1 | 1:1, 3:1, 5:1 |
| 6 | 1:3, 5:1, 7:1 | 1:3, 3:1, 5:1 |
| 7 | 1:2, 2:1, 4:1, 14:1, 17:1 | 1:2, 2:1, 7:1 |
| 8 | 1:3, 3:1, 6:1 | 1:1, 3:1, 4:1, 7:2, 12:1 |
| 9 | 1:7, 2:2, 4:1, 5:2, 7, 8, 11, 18, 29 | 1:4, 2:1, 5, 7, 9, 10, 11, 34 |
| 10 | 1:3, 25, 52, 58 | 1:2, 2:1, 3, 8, 11, 40, 97 |
| 11 | 1:6, 2:1, 4, 5, 55, 68, 113 | 1:3, 2:1, 3, 4, 5, 7, 15, 28, 80 |
| 12 | 1:2, 15, 25, 48, 115, 494 | 1:2, 9, 10, 29, 49, 461 |
| 13 | 1:6, 3:2, 8, 10, 18, 26, 66, 186, 195, 277, 299, 408 | 1:5, 10:2, 20, 37, 51, 116, 210 |
| 14 | 1:2, 5, 17, 19, 44, 204, 578 | 1:5, 2:1, 3, 6, 10, 12, 90, 271 |
| 15 | 1:8, 4, 9, 10, 11, 36, 47, 51, 90, 115, 118, 210, 2497 | 1:6, 2:1, 29, 103, 160, 223, 871, 1493 |
| 16 | 1:5, 2:1, 4, 13, 60, 97, 410, 857, 2678 | 1:3, 24, 137, 274, 570, 1590 |
| 17 | 1:5, 2:1, 5, 8, 9, 13, 23, 41, 58, 63, 102, 760, 1612, 9115 | 1:5, 24, 35, 62, 89, 433, 2235 |

A bare number is a length with one cycle. 2-cycles under `0^0 = 0` occur
in bases 3, 5, 7, 9 (two), 11, 16 and 17. They do not occur in bases 13
and 15. So the lead "every odd base, no even base" holds up to 11 and fails
after it.

### 20.3 The parity invariant

Theorem 20.2 (proven). Let `b >= 3` and `q >= 2`. Then `F(n) == n (mod q)`
for every `n >= 1` if and only if `q = 2`, `b` is odd and `0^0 = 0`.

Proof. Suppose that the congruence holds for all `n`. Take `n = x` for a
digit `x >= 1`: `x^x == x (mod q)`. Take `n = b`, with digits `(1, 0)`:
`1 + m == b (mod q)`. Take `n = b + 1`, with digits `(1, 1)`:
`2 == b + 1`, so `b == 1 (mod q)`, and then `m == 0 (mod q)`, so `m = 0`.
The digit 2 exists because `b >= 3`, so `4 == 2 (mod q)` and `q = 2`.
Then `b == 1 (mod 2)`. Conversely, for odd `b` every `n` is congruent mod 2
to its digit sum, because `b == 1 (mod 2)`. Also `x^x == x (mod 2)` for
`x >= 1` and `w(0) = 0`. So `F(n) == digit sum == n (mod 2)`.

Corollary 20.3 (proven). In an odd base under `0^0 = 0`, the even numbers
below `b^b` form a set that `F` maps into itself, and so do the odd ones.
Each set contains a cycle. So every odd base has a cycle of even numbers,
and has at least one cycle besides the fixed point 1.

Proof. Theorem 20.2 and Proposition 20.1 give two invariant finite sets. A
map from a finite nonempty set into itself has a cycle. The fixed point 1 is
odd.

The census agrees: the odd bases 3 to 17 have 2, 3, 3, 10, 6, 10, 8 and 8
cycles of even numbers. Every cycle in an odd base under `0^0 = 0` has a
constant parity string, for example `parity=00` for both 2-cycles of base 9.

Under `0^0 = 1` an odd base has `F(n) == n + z(n) (mod 2)`, where `z(n)`
counts zeros. The parity flips when `n` has an odd number of zeros. In an
even base `n mod 2` is the last digit and no residue is invariant
(Proposition 10.2 and Theorem 20.2).

### 20.4 Cycles that come in pairs

Proposition 20.4 (proven). A cycle whose members have no digit 0 is a cycle
under both conventions.

Proof. `F_1(n) = F_0(n) + z(n)` (Proposition 1.4), and `z(n) = 0` for every
member.

Proposition 20.5 (proven). Under `0^0 = 0`:

- if every member of a cycle ends in 0, adding 1 to every member gives a
  cycle of the same length;
- if every member has the digit 0 at position `k`, and `a` is self-paying at
  position `k`, adding `a b^k` to every member gives a cycle of the same
  length.

Proof. In both cases each member changes by an amount `delta` and its image
changes by the same `delta`: `F(n + 1) = F(n) + 1` when `n` ends in 0
(Proposition 2.1), and `F(n + a b^k) = F(n) + a^a = F(n) + a b^k`. So the
shifted members form a cycle.

The census has 6 shared cycles of length 2 or more: the 2-cycles of bases
3, 7 and 9, the 3-cycle of base 8, the 5-cycle of base 9 and the 4-cycle of
base 11. So three of the seven 2-cycles of odd bases under `0^0 = 0` are
also 2-cycles under `0^0 = 1`. That explains the 2-cycles of bases 3, 7
and 9 under `0^0 = 1`. Twin cycles (Proposition 20.5) occur only among
fixed points, for example `(4,0,0)` and `(4,0,1)` in base 8. No cycle of
length 2 or more has all members ending in 0.

Neither proposition pairs up 2-cycles inside one convention. I found no
involution on 2-cycles. The data in section 20.6 say that none is needed.

### 20.5 A random-mapping model with the invariant

A uniform random mapping on `N` points has about Poisson(`1/L`) cycles of
length `L` (Flajolet and Odlyzko 1990). The map `F` is not uniform: the
length of `S(c)` and its residue mod `b-1` are fixed by `c`. The model below
keeps exactly this information.

A class `K = (d, r)` is the set of `d`-digit multisets with digit sum
`r (mod b-1)`. Each multiset gets the weight of the number of `d`-digit
strings with nonzero leading digit that have it. In the model, the image of
`c` is a random multiset of the class of `S(c)`, drawn with these weights.
Let `M` be the matrix of class transitions. The trivial fixed point 1 forms
its own class `(1, 1)`, and I remove it.

Proposition 20.6 (proven within the model). The expected number of cycles
of length `L` is

    E_L = (1/L) * (sum over L-tuples of distinct multisets of the product
           of their transition probabilities)
        = (1/L) tr(M^L) - (terms with a repeated multiset).

Proof. A cycle `c_1 -> ... -> c_L -> c_1` of distinct multisets occurs with
the product of the transition probabilities, and each cycle is counted `L`
times by its rotations. Summing over all tuples instead of distinct ones
gives `tr(M^L)`, because the transition probability depends on the source
only through its class.

The repeated terms are small when the classes are large. The script uses
`E_L = (1/L)(tr(M^L) - s + sum over s of exp(-L^2 / (2 N_s)))`, where `s`
counts the eigenvalues near 1 and `N_s` is one over the collision
probability of each closed part. That is the finite-size factor of a
uniform random mapping on `N_s` points.

The spectrum explains the parity effect.

- Odd base, `0^0 = 0`: by Theorem 20.2, `M` splits into two blocks, even and
  odd, each stochastic. So the eigenvalue 1 has multiplicity 2, and
  `E_L ~ 2/L` for large `L`.
- Odd base, `0^0 = 1`: the parity flips with the parity of the number of
  zeros. For `d` random digits `E[(-1)^z] = (1 - 2/b)^d`, about `e^-2`. So
  `M` has eigenvalues 1 and about `e^-2 = 0.135` for large `b` (0.19 and
  0.16 in bases 15 and 17), and
  `E_L ~ (1 + 0.135^L)/L`. For `L = 1` this is the factor `1 + e^-2` of
  section 5.3.
- Even base: one eigenvalue 1.

In all six cases of bases 15 to 17, the largest eigenvalue below 0.9 lies
between 0.10 and 0.19. It comes from the lengths and the residues, and its
square is at most 0.04, so it barely changes `E_2`.

`analysis/dyn_cycle_model.py` computes `M` exactly from the census pass. For
bases 13 to 17, `E_2` is 1.01 to 1.05 in odd bases under `0^0 = 0` and
0.51 to 0.55 otherwise. A model without residues gives 0.51 to 0.52 for
every base, so the doubling comes from the residue mod 2 alone.

### 20.6 Comparison (computed against heuristic)

Bases 3 to 17, observed cycles against the model, without the fixed point 1.
In parentheses: `P(X <= observed)` and `P(X >= observed)` for a Poisson
variable with the model's mean.

| group | `L = 1` | `L = 2` | `L = 3` | `L = 4` | `L = 5` | all lengths |
|---|---:|---:|---:|---:|---:|---:|
| odd, `0^0 = 0` | 32 / 20.6 | 7 / 7.9 (0.47, 0.67) | 2 / 4.8 | 5 / 3.5 | 4 / 2.7 | 92 / 94.4 |
| odd, `0^0 = 1` | 21 / 12.5 | 5 / 4.4 (0.72, 0.45) | 2 / 2.5 | 1 / 1.8 | 3 / 1.4 | 61 / 52.5 |
| even, `0^0 = 0` | 15 / 8.3 | 1 / 3.5 (0.13, 0.97) | 1 / 2.2 | 1 / 1.6 | 2 / 1.3 | 41 / 42.6 |
| even, `0^0 = 1` | 12 / 8.5 | 3 / 3.8 (0.47, 0.73) | 4 / 2.3 | 1 / 1.7 | 1 / 1.3 | 43 / 43.4 |

What this shows:

- The total number of cycles matches the model in all four groups.
- Fixed points are in excess by a factor of 1.4 to 1.8. The constructions of
  chapter 2 and the small bases of section 5.4 cause this, as known.
- 2-cycles in odd bases under `0^0 = 0`: 7 against 7.9. The parity
  invariant explains the factor 2, and nothing more is needed.
- 2-cycles in even bases under `0^0 = 0`: 1 against 3.5. A Poisson variable
  with mean 3.5 is at most 1 with probability 0.13.

The lead as stated (2-cycles in all odd bases 3 to 11, none in even bases 4
to 10) has model probability `0.081 * 0.141 = 0.011`. That is small, but
the pattern was chosen after looking at the data, and it breaks at bases 13,
15 and 16. I conclude that the lead is the parity doubling of Theorem 20.2
plus chance.

## 13. Bases with two 2-digit solutions

Theorem 13.1 (proven). Under `0^0 = 1`, base 3 is the only base with two
2-digit solutions, `(1,2)` and `(2,2)`. Under `0^0 = 0` the bases with two
2-digit solutions are base 3 and the bases `a^(a-1)` with `a >= 3`, which
have the twins `(a,0)` and `(a,1)`. No base has three.

The proof does not use the condition that the digits are below the base,
except in the case `A = 2`.

Proof. Let `(a, c)` and `(A, C)` be 2-digit solutions in base `b`. By
Proposition 2.6,

    (1)  a b = a^a + g(c),      (2)  A b = A^A + g(C).

If `a = A`, then `g(c) = g(C)`. Under `0^0 = 1`, `g(0) = 1`, `g(1) = 0` and
`g` is strictly increasing from 1 on, so `g` is injective and `c = C`. Under
`0^0 = 0`, `g(0) = g(1) = 0` gives the twins, and otherwise `c = C`.

So let `a < A`. Since `g >= 0`, (2) gives `b >= A^(A-1)`. Write
`b = A^(A-1) + u` with `u >= 0`. Then (1) and (2) become

    (3)  g(c) = a A^(A-1) - a^a + a u,      (4)  g(C) = A u.

If `A = 2`, then `a = 1`, and `b > A` forces `u >= 1`. So `g(c) >= 2`.

Step 1: `c >= A`. For `A >= 3`, (3) gives
`g(c) >= a (A^(A-1) - a^(a-1)) >= A^(A-1) - (A-1)^(A-2)`, which exceeds
`g(A-1) = (A-1)^(A-1) - (A-1)` because `A^(A-2) > (A-1)^(A-2)`. Every `c`
with `c <= A-1` has `g(c) <= g(A-1)` (here `g(A-1) >= 2 >= g(0)`). So
`c >= A`. For `A = 2`, `g(c) >= 2` gives `c >= 2`.

Step 2: `C <= c`. Suppose `C >= c + 1`. For `c >= 2`,
`g(c+1) = (c+1)^(c+1) - (c+1) >= 2 (c+1) g(c)`, because
`(c+1)^(c+1) >= 2.25 (c+1) c^c`. With (3) and (4),
`A u = g(C) >= 2 (c+1) g(c) > 2 (c+1) a u`. If `u = 0` then `g(C) = 0` and
`C = 1 < c`. If `u > 0` then `A > 2 a (c+1) >= 2 (A+1)`, which is false.

Step 3: `c = A`. From `g(C) <= g(c)`, (3) and (4) give
`u (A - a) <= a A^(A-1) - a^a`. Put this into (3):
`g(c) <= (a A^(A-1) - a^a) A / (A - a) < (A-1) A^A < g(A+1)`. So `c <= A`,
and with step 1, `c = A`.

Step 4. With `c = A`, (1) gives `b = (a^a + A^A - A) / a`. Then (2) gives

    a g(C) = A^A (A - a) + A a^a - A^2.

Since `C <= c = A`, `a g(C) <= a (A^A - A)`, which means

    (5)  A^A (A - 2a) + A (a^a + a - A) <= 0.

If `a = 1`, (5) reads `(A - 2)(A^A - A) <= 0`, so `A = 2`. If `a >= 2` and
`A >= 2a`, the left side of (5) is positive: for `A = 2a` it is
`A (a^a - a) > 0`, and for `A > 2a` it is at least `A^A - A^2 > 0`. So
`a < A < 2a`. Then `a g(C) >= A^A + A a^a - A^2 > a A^(A-1)`, so
`g(C) > A^(A-1) > g(A-1)` and `C >= A`. With `C <= A`, `C = A`, and
`g(C) = A^A - A`. The displayed equation becomes
`A^(A-1) (2a - A) = a^a + a - A`. The left side is at least
`A^(A-1) >= (a+1)^a > a^a + a - A`, a contradiction.

So `a = 1`, `A = 2`, `c = 2`, and `g(C) = 2`, so `C = 2`. The base is
`(1 + 2) / 1 = 3`. Three 2-digit solutions in one base would give two with
different leading digits, which happens only in base 3, and base 3 has
exactly two.

Check (computed). `analysis/dyn_two_digit.py` lists every 2-digit solution
with `a <= 200` and `c <= 3000`, that is bases up to about `10^10400`. Under
`0^0 = 1` only base 3 has two. Under `0^0 = 0`, 199 bases have two: base 3
and the 198 twin bases. The inequalities of steps 1 to 4 hold on the grid
`A <= 60`.

## 16. Cores in bases with self-paying digits

Under `0^0 = 0` a solution splits into a core, self-paying digits and an
optional final 1 (Proposition 2.3). The question asks whether only finitely
many nonzero cores sit in bases with a self-paying digit.

Proposition 16.1 (proven). Write `b = r^t` with `r` not a perfect power.
Base `b` has a self-paying digit if and only if `t` has a prime factor that
does not divide `r`.

Proof. By Proposition 2.2 we need `1 <= s < t` with `t | s (r^s - 1)`. Write
`t = U V`, where `V` collects the prime powers of `t` whose primes divide
`r`, and `U` the rest. `r^s - 1` is coprime to `r`, so `V` must divide `s`.
If `U = 1`, then `t | s` with `s < t`, which is impossible. If `U > 1`, take
`s = V * ord_U(r)`. Then `U | r^s - 1` and `V | s`, so `t | s (r^s - 1)`,
and `s <= V phi(U) < U V = t`.

So 4, 16, 27, 36 and 100 have no self-paying digit, as chapter 2 lists, and
every base `r^p` with `p` prime and `p` not dividing `r` has one.

Theorem 16.2 (proven). For every `a >= 2`, the 2-digit swap `(a, a^a)` is a
core in a base with a self-paying digit. So infinitely many nonzero cores do.
If `a` is not a perfect power, then

    (a^(a+1), 0, ..., 0, a, a^a)    (a + 2 digits)

is a solution in base `a^(a^(a+1) - 1)` under `0^0 = 0`. For `a = 2` it is
`(8, 0, 2, 4)` in base 128.

Proof. The swap of section 2.3 with `k = 1` is `(a, a^a)` in base
`B = a^(a^(a+1) - 1)`. Write `a = r^u` with `r` not a perfect power. Then
`B = r^t` with `t = u (a^(a+1) - 1)`. The factor `a^(a+1) - 1 > 1` is
coprime to `r`, so Proposition 16.1 applies. Explicitly, `s = u (a+1)` gives
the digit `r^s = a^(a+1)`, and `s (r^s - 1) = t (a+1)`, so it is
self-paying at position `a + 1`. The core occupies positions 0 and 1, and
position `a + 1 >= 3` is free, so Proposition 2.3 gives the solution.

So the literal question has the answer no. The real question is whether the
swaps are the only infinite source.

Computed (`analysis/dyn_two_digit.py`). Among the 2-digit solutions with
`a <= 200` and `c <= 3000` under `0^0 = 0`, excluding `(a,0)` and `(a,1)`,
exactly 4 have a perfect-power base: `(1,3)` in `5^2`, and the swaps
`(2,4)` in `2^7`, `(3,27)` in `3^80` and `(4,256)` in `2^2046`. All four
bases have a self-paying digit. Among all 1,779 known solutions under
`0^0 = 0` with at least 2 digits (`analysis/dyn_cores.py`), 3 combine a
nonzero core with a self-paying digit: `(5,1,3)` in base 25, `(8,0,2,4)` in
base 128 and `(3,0,0,0,9,27)` in base `3^16`.

Theorem 16.3 (proven, assuming the abc conjecture). Fix `delta > 0`. Only
finitely many 2-digit solutions `(a, c)` under `0^0 = 0` with `c >= 2`,
`c != a^a` and a perfect-power base satisfy

    min(a^a, c^c) <= max(a^a, c^c)^(1/4 - delta).

Proof. Let `b = r^t` with `t >= 2`, so `r <= b^(1/2)`. Use abc in the form
`z / gcd <= K_eps rad(x y z)^(1 + eps)` for `x + y = z`.

Case `c^c > a^a`, so `c > a`. Write `a r^t = c^c + D` with
`D = a^a - c != 0`. Then `|D| <= max(a^a, c)`, and `gcd(a r^t, c^c)` divides
`D`. Since `b <= 2 c^c`, `r <= 2 c^(c/2)`. abc gives
`c^c <= K |D| (a r c |D|)^(1 + eps) <= c^(c/2 + O(1)) |D|^(2 + eps)`, up
to a factor `c^(O(eps c))`. With `|D| <= c^(c (1/4 - delta)) + c` the right
side is `c^(c (1 - 2 delta) + O(eps c) + O(1))`. For small `eps` this is
below `c^c` once `c` is large. So `c`, and then `a < c`, are bounded.

Case `a^a > c^c`, so `a > c >= 2`. Write `a r^t = a^a + E` with
`E = c^c - c > 0`, and `gcd(a r^t, a^a)` divides `E`. Now `b <= 2 a^(a-1)`,
so `r <= 2 a^(a/2)`, and the same computation with
`E <= a^(a (1/4 - delta))` bounds `a`.

Each pair `(a, c)` has one base, so the set is finite.

The theorem leaves out the case `a^a ~ c^c`, where the equation has four
large terms and abc does not apply. Heuristic: the
number of perfect powers among the 2-digit bases is
`sum over (a, c) of b^(-1/2)`, which converges fast. So I expect that the
swaps and `(1,3)` in base 25 are all 2-digit cores in perfect-power bases.
For long cores the model gives the same answer. A core with about `b`
digits sits on a self-paying position with probability about `1/b`, and
the bases with self-paying digits are the odd squares and sparser sets.
That sum, `sum over odd r of 2/r^2`, also converges.

One unconditional case. For the family `(1, c)`, the base is
`c^c - c + 1`. If `t | c`, it is not a `t`-th power: with `Y = c^(c/t)` it
lies strictly between `(Y-1)^t` and `Y^t`, because
`Y^t - (Y-1)^t >= Y^(t-1) >= c^(c/2) > c - 1`.

## 14. Coverings beyond parity

### 14.1 What section 1.6 gives

For a string `s` with `k` digits, `Q_s(r) = sum s_i r^(k-1-i) - F(s)` must
vanish at `r = b`. The rules of section 1.6 look at bases `b == 1 (mod q)`
(the digit sum) and at even bases (the last digit). Modulo 2 these are all
residues.

Proposition 14.1 (proven). `Q_s` has no root mod 2 exactly when both parity
rules of section 1.6 fail for `s`: `Q_s(1)` odd excludes every odd base and
`Q_s(0)` odd excludes every even base.

Proof. `Q_s(0) = s_last - F(s)` and `Q_s(1) = digit sum - F(s)`. For odd `b`,
`Q_s(b) == Q_s(1) (mod 2)`. For even `b`, `Q_s(b) == Q_s(0) (mod 2)`.

So a covering that uses only the modulus 2 reduces to section 1.6. Any
covering that needs another modulus excludes bases in residue classes that
section 1.6 does not touch, such as `b == 2 (mod 3)`.

### 14.2 The values of `x^x - x`

A varying last digit `x` enters `Q_s` as `x - x^x`. So the set
`T(q) = { x^x - x mod q : x >= 1 }` decides which coverings exist.

Lemma 14.2 (proven).

1. For `q = 2^e`, `T(q)` is the set of even residues.
2. For a prime `p >= 5`, `T(p)` is all of `Z/p`. `T(3) = {0, 2}`.
3. For every `x >= 1`: if `x == 2 (mod 6)`, then `x^x - x == 2 (mod 27)`.
   Otherwise `x^x - x == 0 (mod 3)`. So `T(9) = {0, 2, 3, 6}` and
   `T(27) = 3Z/27 + {2}`.

Proof. (1) `x^x == x (mod 2)`. For `e >= 1` every even residue occurs, for
example at even `x >= e` where `x^x == 0`.

(2) `x = 0 (mod p)` gives 0. For `v != 0`, pick a primitive root `u` with
`u != -v`; `p >= 5` has at least 2 primitive roots. Then `u + v` is a unit,
so `u + v = u^j` for some `j`. By the Chinese remainder theorem some `x` has
`x == u (mod p)` and `x == j (mod p-1)`, and then `x^x - x == v`. For `p = 3`
the only primitive root is 2, and the computation in (3) gives `{0, 2}`.

(3) If `x == 0 (mod 3)`, both terms are `0 mod 3`. If `x == 1 (mod 3)`,
`x^x == 1`. If `x == 5 (mod 6)`, `x^x == (-1)^x == -1 == x (mod 3)`. Now let
`x == 2 (mod 6)`, so `x` is even and `3 | x + 1`. Put `u = -x = 1 + 3t` with
`3t = -(x+1)`. Since `x` is even, `x^x = u^x`, and modulo 27

    u^x == 1 + x (3t) + C(x,2) (3t)^2 = 1 - x (x+1) + x (x-1) (x+1)^2 / 2,

because `(3t)^3` and higher powers vanish. So
`x^x - x == 2 + (x+1)^3 (x-2)/2 (mod 27)`, and `27 | (x+1)^3`.

For `q = 25`, `T(25)` misses 3, 13, 18 and 23 (computed). For 49, 121, 169,
289 and 361, `T(q)` is everything (computed).

### 14.3 A covering theorem

Theorem 14.3 (proven). Let `(s_1, ..., s_(k-1))` be a prefix, let
`A(r) = sum s_i r^(k-i)` and `F_0 = sum w(s_i)`. Suppose that for every
residue `r mod 27`,

    A(r) - F_0 != 0 (mod 3)   and   A(r) - F_0 != 2 (mod 27).

Then no string `(s_1, ..., s_(k-1), x)` with `x >= 1` is a solution in any
base, under either convention. Under `0^0 = 0` this also holds for `x = 0`.

Proof. A solution in base `b` gives `A(b) - F_0 = x^x - x` (for `x = 0`
under `0^0 = 0`, the right side is 0). By Lemma 14.2 the right side is
`0 (mod 3)` or `2 (mod 27)`.

Example. `(2, 1, x)`: `A(r) - F_0 = 2r^2 + r - 5` takes the values 1, 1, 2
mod 3 at `r = 0, 1, 2`, and `2r^2 + r` is 1 or 10 mod 27 for `r == 2 (mod 3)`,
never 7. So `(2, 1, x)` is never a solution, for every `x >= 1`. The string
`(2, 1, 0)` has `Q = (2r - 3)(r + 2)` under `0^0 = 1`, with no root above 2.
The digit `x` can be as large as we like, so this excludes bases up to
infinity in one stroke.

The same theorem covers `(2, y, x)` and `(8, y, x)` for
`y = 1, 2, 3, 4, 6, 8, 9, 10`, and many longer prefixes.

### 14.4 The search (computed)

`analysis/dyn_cover.py` uses the prime powers 2, 4, 8, 16, 32, 3, 9, 27,
5, 25, 7, 49 and the primes 11 to 47. A family with varying digit `x` at
any position is covered when every class of `x mod lcm(q, lambda(q))` has
no root for some modulus. The script finds a covering greedily and prunes
it to a minimal set. It checks `x < 8` exactly.

| length | fixed digits | `0^0` | families | covered | by parity alone | need another modulus |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | `<= 10` | 1 | 341 | 27 | 5 | 22 |
| 3 | `<= 10` | 0 | 341 | 19 | 0 | 19 |
| 4 | `<= 5` | 1 | 756 | 93 | 26 | 67 |
| 4 | `<= 5` | 0 | 756 | 17 | 0 | 17 |
| 5 | `<= 3` | 1 | 1024 | 163 | 40 | 123 |
| 5 | `<= 3` | 0 | 1024 | 68 | 0 | 68 |

The minimal modulus sets: `{4}` 106 times, `{9}` 91, `{3}` 32, `{3,4}` 24,
`{27,4}` 16, `{8}` 10, `{16}` 10, `{9,4}` 6, and 11 sets that contain 5 or
25. One covering uses the prime 11: `(2,0,1,0,x)` under `0^0 = 1` has no
root mod 8, 11 or 25 for each `x`. I checked it directly for
`6 <= x < 20000`.

The `{3}` coverings are of a special kind. For `(1,3,2,x)`,
`r^3 + 3r^2 + 2r == r^3 - r == 0 (mod 3)` for every `r`. So `n mod 3` does
not depend on the base, and the digit-sum rule of section 1.6 extends to
all bases.

Density (computed, `analysis/dyn_cover_density.py`, 20,000 random prefixes
with digits in `[3, 10^6]`). Share of prefixes for which the last digit is
covered:

| length | by 27 alone | by 16 alone | by 16, 27, 25 and 7 |
|---:|---:|---:|---:|
| 3 | 0.112 | 0.000 | 0.112 |
| 4 | 0.072 | 0.000 | 0.072 |
| 5 | 0.079 | 0.000 | 0.082 |
| 6 | 0.084 | 0.000 | 0.086 |

Answer to question 14: coverings beyond parity exist, and they are not
rare. About one prefix in twelve makes its last digit impossible in every
base, and almost all of that is Theorem 14.3. Section 11.3 expected no such
coverings because it used primes only, and `T(p) = Z/p` for `p >= 5`. The
prime powers `3^e` carry the structure, through the coupling of `x mod 3^e`
and `x mod 2 * 3^(e-1)`.

## 15. Constructions under `0^0 = 1` from power identities

Theorem 15.1 (proven). Let `b = r^t`. For `0 <= u < t` put
`phi(u) = u r^u mod t` and `pi(u) = floor(u r^u / t)`. Choose `u_0 >= 1` and
follow `u_(i+1) = phi(u_i)` until `u_j = 0`. Place `c = r^(u_0)` at
position 0 and `r^(u_(i+1))` at position `pi(u_i)`. Add any set of cycles
`(v_1, ..., v_l)` of `phi` on `1..t-1`, with `r^(v_i)` at position
`pi(v_(i-1))`, indices mod `l`. If all positions differ and the number has
exactly `c - 1` zeros below its leading digit, it is a solution under
`0^0 = 1`.

Proof. The digit `r^(phi(u))` at position `pi(u)` has the value
`r^(phi(u) + t pi(u)) = r^(u r^u) = w(r^u)`. So each chain digit before the
last pays for the weight of its predecessor, and each cycle digit pays for
the weight of the previous one in its cycle. The weights left over are the
1 of the final digit 1 and `c - 1` for the zeros. Their sum is `c`, the
value of the digit at position 0. The digits are below `b` because
`u < t`.

Cycles of length 1 are the self-paying digits, cycles of length 2 are swaps.
The 11-digit solution of base 64 is the chain `3 -> 0` (`8` at position 0,
`1` at position 4), plus the self-paying digits 4 and 16, with 7 zeros. The
solutions `(a, 1)` are the case `u_0 = 0`, without zeros.

Multiplicity. If the chain reaches position `T` and `n` self-paying digits
sit below `T` off the chain, then every set of `k = T - j - c + 1` of them
gives a solution. That would give `C(n, k)` solutions in one base, so the
mechanism can in principle produce `N_1(b) >= 6`. It needs the near
coincidence `pi(u_i) ~ c` for some chain element, with an error of at most
`log2 b`.

Computed (`analysis/dyn_power_digits.py`). For all bases `r^t` with
`2 <= r <= 40` (not a perfect power) and `2 <= t <= 300`, the construction
gives 43 solutions. 42 are `(a, 1)` in base `a^(a-1)`. The other one is the
11-digit solution of base 64. No base gets more than 2. Exact integer checks
confirm every solution with at most 3000 digits.

Answer to question 15: within this range the power identities give no base
with more than 2 constructed solutions. I expect finitely many solutions of
this type beyond the `(a, 1)` family (heuristic: each needs an exact
coincidence between `pi(u)` and `r^(u_0)`). A base with `N_1(b) >= 6` from
constructions alone would need the multiplicity mechanism above, and the
search found no instance of it.

## 30. Integers with several bases

Proposition 30.1 (proven). Under `0^0 = 0`, let `c = r^u` with `r` not a
perfect power. Then `N = c^c + 1` is a solution in every base `r^t` with
`u < t` and `t | u (c - 1)`, and in base `c^c - c + 1`. So one integer can be
a solution in arbitrarily many bases.

Proof. In base `r^t` the digit `c` is self-paying at position
`k = u (c-1) / t`, so `(c, 0, ..., 0, 1)` with `k + 1` digits is a solution
(Proposition 2.3), and its value is `c^c + 1`. The base `c^c - c + 1` has the
solution `(1, c)`. The number of divisors of `u (r^u - 1)` is unbounded.

For `c = 256 = 2^8`, `8 * 255 = 2040` has 25 divisors above 8. So
`2^2048 + 1` is a solution in 26 bases. The complete search below confirms
that these 26 are all.

Proposition 30.2 (proven). Under `0^0 = 1`, an integer `N >= 3` has at most
two 2-digit representations as a solution. If it has two, they are `(a, c)`
and `(c, a)` with `N = a^a + c^c`, `a | c^c - c` and `c | a^a - a`.

Proof. A 2-digit solution has `N = w(a) + w(c)`. If `X^X + Y^Y = U^U + V^V`
with `X >= Y`, `U >= V` and `X > U`, then `X^X >= (U+1)^(U+1) > 2 U^U`, a
contradiction. So the pair of weights is unique. The weight 1 belongs to
both 0 and 1. `(a, 0)` needs `a | 1`, so it is `(1, 0)` in base 2 with
`N = 2`. The two orders of the pair give at most two strings, and
Proposition 2.6 gives the divisibility conditions.

So `N = c^c + 1`, with `(1, c)` and `(c, 1)`, has two bases for every
`c >= 2`. A third base needs a representation with 3 or more digits.

Proposition 30.3 (proven). Let `X` be the largest integer with `X^X <= N`.
If `N` is a solution in base `b` with `k` digits and leading digit `p`, then
`b <= (N/p)^(1/(k-1)) < b + (X+1) / (p (k-1))`.

Proof. Every digit `d` of a solution has `d^d <= F(N) = N`, so `d <= X`.
With the second digit at most `X`, `p b^(k-1) <= N < (p + (X+1)/b) b^(k-1)`,
and the mean value theorem gives the bound.

So `analysis/dyn_multibase.py` finds every base of `N`: it checks bases up
to 1000 directly, and for larger bases only the few candidates of
Proposition 30.3 for each `k` and `p`.

Computed. Candidates: every known solution and every `a^a + w(c)` with
`a, c <= 40`.

- Under `0^0 = 1`: of 1,410 candidates, 201 are solutions in exactly 2
  bases and none in 3. None of them has a representation with 3 or more
  digits.
- Under `0^0 = 0`: 428 have 2 or more bases, and 272 have a representation
  with 3 or more digits. All of these come from Proposition 30.1 and its
  twin `c^c` (bases `r^t` only). The maximum is 26, for `2^2048 + 1`.

Answer to question 30: under `0^0 = 0` the count is unbounded, through
self-paying digits. Under `0^0 = 1` every known multi-base integer is a
2-digit pair, at most 2 bases come from 2 digits, and a third base would
need a coincidence of the kind of chapter 3. I do not know a reason why one
cannot exist.

## New questions

1. (from 20) Even bases under `0^0 = 0` have 1 2-cycle against 3.5
   expected in bases 4 to 16. Is there a second invariant, or is this
   chance? Base 18 (45 minutes per convention) and a 2-cycle search by
   meet in the middle would tell.
2. (from 20) Six of the short cycles are zero-free and so shared between
   conventions. The model predicts about `e^(-L)` of `L`-cycles to be
   zero-free. Is the observed share larger?
3. (from 14) Does every covering use a modulus `q` with `T(q) != Z/q`,
   that is a power of 2, 3 or 5? The covering of `(2,0,1,0,x)` uses 11, but
   together with 8 and 25.
4. (from 14) Theorem 14.3 excludes about 8% of all prefixes. Does it explain
   part of the 2x to 4x excess of the sieve in question 28?
5. (from 16) Is `(1,3)` in base 25 the only 2-digit core in a perfect-power
   base that is not a swap? That needs the case `a^a ~ c^c` of
   Theorem 16.3.
6. (from 15) Is there a base `r^t` where a chain reaches a position above
   `r^(u_0)` with several self-paying digits below it? That would give
   `C(n, k)` solutions under `0^0 = 1`.
7. (from 30) Is there an integer with 3 bases under `0^0 = 1`?

## Scripts and data

| file | produces |
|---|---|
| `fast/src/bin/dyn_cycles.rs` | the cycle census and the class transition matrices |
| `analysis/dyn_cycle_model.py` | model predictions for each cycle length (`analysis/data/dyn_cycle_model.txt`) |
| `analysis/data/dyn_cycles.txt` | every cycle in bases 3 to 17, both conventions |
| `analysis/dyn_two_digit.py` | bases with two 2-digit solutions, perfect-power 2-digit bases |
| `analysis/dyn_cores.py` | cores of all known solutions under `0^0 = 0` |
| `analysis/dyn_cover.py` | coverings with prime powers (`analysis/data/dyn_cover.txt`) |
| `analysis/dyn_cover_density.py` | share of covered prefixes |
| `analysis/dyn_power_digits.py` | chain-and-cycle solutions under `0^0 = 1` |
| `analysis/dyn_multibase.py` | every base of a given integer |

To rebuild the matrices for the model, run
`fast/target/release/dyn_cycles <b> <m> --matrix fast/target/dyn/mat_<b>_<m>.txt --model-only`
for `b` from 3 to 17 and both `m`. This takes about 4 minutes in total.
