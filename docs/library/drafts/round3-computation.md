# Round 3 computations: a faster sieve, short-string spectra, narcissistic numbers

Draft for questions 47, 49, 48, 58 and 57 of `questions-round3.md`, in that
order. Every statement is marked:

- proven: the proof is here;
- computed: an exact computation found it, and the range is stated;
- heuristic: the root heuristic of section 11.4 or the refined model of
  chapter 5, which are not proofs.

Scripts are in `analysis/` with names starting `r3c_`. Their output is in
`analysis/data/r3c_*`. Timings were taken while other jobs kept the load
average of the 8-thread test machine at 20 to 36, so they are slower than on
an idle machine. Each comparison of two programs alternated their runs.

## Summary

SUMMARY

## 47. Prime powers in the sieve of `kdigit`

### 47.1 Any modulus works, and only prime powers add anything (proven)

Proposition 11.1 holds for every modulus `q`, with the same proof: if
`Q_s(b) = 0`, then `b mod q` is a root of `Q_s` modulo `q`. `Q_s(r) mod q`
depends only on `r mod q`, because `Q_s` has integer coefficients. The mask
method of section 11.5 therefore works for any `q`. It needs `w(x) mod q`
for every digit `x` up to `M`, and `kdigit` computes these residues one digit
at a time. So the period of `x^x mod q` in `x` (it divides
`lcm(q, lambda(q))`) never enters the program.

Two facts limit the useful moduli to one power of each prime:

- If `q = q_1 q_2` with `gcd(q_1, q_2) = 1`, then `Q_s` has a root mod `q`
  exactly when it has a root mod `q_1` and a root mod `q_2` (Chinese
  remainder theorem). A composite modulus with two prime factors tests
  nothing new.
- A root mod `p^e` reduces to a root mod `p^f` for `f < e`. So `p^e` removes
  every string that `p^f` removes, and the test mod `p^f` is redundant after
  it.

### 47.2 How much each modulus removes (computed)

`kdigit --stats` counts, for each modulus in the order of the list, the
candidate strings it tests and removes. A candidate is a string with one
convention; a string without the digit 0 counts once. Share of the
candidates that one modulus removes when it is tested first
(`r3c_kdigit_moduli.py singles`, data `r3c_kdigit_singles.txt`):

| modulus | k = 3, M = 80 | k = 4, M = 44 | k = 5, M = 28 | k = 6, M = 16 |
|---|---:|---:|---:|---:|
| 2 | 0.012 | 0.030 | 0.055 | 0.092 |
| 4 | 0.169 | 0.141 | 0.205 | 0.245 |
| 8 | 0.237 | 0.184 | 0.255 | 0.295 |
| 16 | 0.266 | 0.207 | 0.287 | 0.326 |
| 32 | 0.286 | 0.218 | 0.298 | 0.336 |
| 64 | 0.295 | 0.223 | 0.306 | 0.344 |
| 128 | 0.300 | 0.224 | 0.308 | 0.346 |
| 3 | 0.204 | 0.229 | 0.253 | 0.281 |
| 9 | 0.336 | 0.334 | 0.370 | 0.397 |
| 27 | 0.386 | 0.350 | 0.391 | 0.417 |
| 81 | 0.408 | 0.356 | 0.403 | 0.429 |
| 5 | 0.306 | 0.318 | 0.326 | 0.328 |
| 25 | 0.416 | 0.362 | 0.403 | 0.402 |
| 125 | 0.430 | 0.365 | 0.411 | 0.409 |
| 7 | 0.356 | 0.325 | 0.333 | 0.339 |
| 49 | 0.459 | 0.353 | 0.393 | 0.392 |
| 11 | 0.414 | 0.335 | 0.351 | 0.350 |
| 121 | 0.491 | 0.348 | 0.392 | 0.384 |
| 61 | 0.485 | 0.333 | 0.371 | 0.365 |
| 127 | 0.496 | 0.333 | 0.373 | 0.366 |
| random polynomial of degree `k-1`, large `p` | 1/2 | 1/3 | 3/8 | 11/30 |

The last row is the share of polynomials of degree `n = k - 1` over a large
prime field with no root, `sum_{j <= n} (-1)^j / j!` (proven, by
inclusion and exclusion over the roots). The large primes match it to 0.002.
Section 11.3 used `1/e` for all lengths.

What the table shows:

- The powers of 2 gain the most: 0.03 to 0.09 for 2, against 0.22 to 0.34
  for 32. The reason is Lemma 15.12: `x^x - x` is always even, so the last
  digit only moves `Q_s` by even amounts mod 2. Mod `2^e`, the even digits
  `x >= e` have `x^x == 0`, and the test sees the value of `x` itself.
- The powers of 3 gain from 0.20 to 0.25 for 3 to 0.35 to 0.42 for 27. The
  values of `x^x - x` mod 27 lie in a set of 10 residues (Lemma 15.12), so
  27 sees the coverings of Theorem 15.13. Beyond 27 the gain is small.
- 25, 49 and 121 remove 0.04 to 0.10 more than 5, 7 and 11.
- Above 32, 27 and 25, the gain per step is below 0.01.

### 47.3 The new sieve (computed)

The prime powers alone do not make the program much faster. The old program
spent its time on the masks, not on the exact root step: it built the mask
of every prime for every prefix of `k - 1` digits, with a division for each
residue. The new `kdigit` changes four things:

- It stores the prefix residues as bytes, for all moduli side by side, and
  adds the precomputed residues of each digit without a division. A sum
  below `2q <= 256` reduces by `min(t, t - q)`.
- It keeps residues only down to the digit of exponent 1. The mask of a
  modulus for the last digit is built only while some last digit is still
  alive. With strong moduli first, the masks of the later moduli are rarely
  needed: for `k = 5, M = 40`, the first mask is built for all 2.76 million
  prefixes and the mask of 127 for 197 of them.
- While more than 12 candidates are alive, each residue outside the mask
  removes a precomputed bit set of digits. Below 12, it tests the candidates
  one by one, without branches.
- Any modulus from 2 to 128 works, with 128-bit masks. The default list is
  32, 27, 25, 49 and the primes 11 to 127, 31 moduli in all.

New options: `--moduli` sets the list, `--stats` prints the counts per
modulus, and `--offset D` finds the strings with `P_s(b) - F(s) = D`
(question 49). `fast/README.md` describes them.

Checks (computed). The new program prints the same lines as the old one for
`k = 2` (`M = 300`), 3 (`M = 200`), 4 (`M = 44`), 5 (`M = 28`), 6 (`M = 20`)
and 7 (`M = 12`). With the old list of 18 primes it passes exactly the same
strings (`--survivors`, `k = 4, M = 44` and `k = 5, M = 20`). It reproduces
the full lists `analysis/data/k4.txt` to `k7.txt` (`M` = 300, 80, 40, 26)
line for line.

### 47.4 Speed (computed)

Old (commit `4e0da21`) against new, 4 threads, best of 2 alternating runs,
load average 25 to 32 (`r3c_kdigit_speed.py`, data `r3c_kdigit_speed.txt`):

| k | M | survivors, old | new | wall time, old | new | speedup |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 150 | 615,113 | 2,089 | 19.5 s | 1.80 s | 10.8 |
| 5 | 60 | 507,922 | 716 | 49.0 s | 3.59 s | 13.6 |
| 6 | 30 | 588,869 | 961 | 76.7 s | 5.83 s | 13.2 |
| 7 | 18 | 596,001 | 1,318 | 125.1 s | 10.3 s | 12.2 |

User time falls by the same factor, 10.8 to 11.3. The full lists, 4 threads
at load average 25 to 35, against the times of section 11.5 (8 threads, a
quieter machine):

| k | M | section 11.5 | new | survivors, old | new |
|---:|---:|---:|---:|---:|---:|
| 4 | 300 | 215 s | 23.7 s | 9,655,743 | 30,337 |
| 5 | 80 | 113 s | 19.8 s | 2,085,723 | 2,604 |
| 6 | 40 | 201 s | 38.9 s | 3,087,035 | 4,419 |
| 7 | 26 | 644 s | 144 s | 6,685,394 | 9,428 |

Which part of the gain comes from the moduli. On one thread, the new code
with different lists (`r3c_kdigit_moduli.py`, data `r3c_kdigit_moduli.txt`):

| list | survivors, k = 4, M = 100 | k = 7, M = 12 | time relative to the 18 primes: k = 4, M = 100 | k = 5, M = 30 | k = 6, M = 16 | k = 7, M = 12 |
|---|---:|---:|---:|---:|---:|---:|
| primes 2 to 61 (old) | 124,102 | 43,694 | 1 | 1 | 1 | 1 |
| 32, 27, 25, 7, 11, primes 13 to 61 | 79,112 | 22,990 | 0.86 | 0.94 | 0.97 | 1.00 |
| 32, 27, 25, 49, 11, primes 13 to 61 | 75,637 | 21,218 | 0.92 | 0.93 | 1.06 | 1.01 |
| 32, 27, 25, 7, 11, primes 13 to 127 | 539 | 636 | 0.89 | 0.92 | 1.00 | 0.99 |
| 64, 81, 125, 49, 121, primes 13 to 61 | 72,543 | 19,301 | 1.46 | 3.22 | 2.81 | 2.42 |

Each time is the best user time of 3 alternating runs on one thread.

In the first version of the new code (lazy masks, but the candidates tested
one by one), the list 32, 27, 25, 7, 11, 13 to 61 was 1.25 to 1.35 times
faster than the 18 primes. After the bit sets, the filter is cheap, and the
list changes the time by less than the noise of about 15%. Large moduli first
(64, 81, 125, 49, 121) cost 1.5 to 3 times more, because their masks are
built for every prefix. So the speedup of 11 is almost all code. The prime
powers and the primes 67 to 127 still matter for the survivors: they pass
300 to 800 times fewer strings to the exact root step. That step dominates
for large `M`, where the numbers have hundreds of digits.

Answer to the question "which set of 18 moduli is best": with lazy masks,
the length of the list costs almost nothing, so the best list is not limited
to 18. The default takes one power of each prime, strong and cheap ones
first: 32, 27, 25, 49, then the primes 11 to 127.

### 47.5 Longer lists (computed)

The speedup pays for longer lists. Two new runs, on 3 threads at load
average about 40 (data `r3c_k7_M32.txt`, `r3c_k8_M22.txt`):

| length | digits up to | complete for bases up to | time | strings | survivors | new solutions |
|---:|---:|---:|---:|---:|---:|---|
| 7 | 32 | `10^7.2` (was `10^5.5`) | 565 s | `4.1 * 10^10` | 36,309 | under `0^0 = 0`: `(27,0,0,0,0,0,0)` and `(27,0,0,0,0,0,1)` in base `3^13`, `(31,0,...,0)` and `(31,0,...,0,1)` in base `31^5`; none under `0^0 = 1` |
K8ROW

The new 7-digit solutions are the self-paying family `(x, 0, ..., 0)` and its
twin, with `x^(x-1)` a sixth power (chapter 2). Under `0^0 = 1` the only
7-digit solution in all bases up to `10^7.2` is still `(1,6,5,6,5,4,7)` in
base 9. By the tail estimate of section 11.4 (`analysis/list_tails.py`),
the expected number of 7-digit solutions with a larger digit is
`1.7 * 10^-33`, and `K8TAIL` for 8 digits.

## 58. Narcissistic numbers as a model test

A `d`-digit narcissistic number in base `b` equals the sum of its digits,
each raised to the power `d`. So the weights are `x^d`, and they change with
the length.

### 58.1 The data (computed)

`fast search` takes a new option `--power p`: the weights become `x^p` for
`x >= 1`. With `--zero 0`, `--min-digits d` and `--max-digits d` it finds
the `d`-digit narcissistic numbers. The test of the weight options compares
`--power` 1, 2, 3, 5 and 8 with a brute force over all digit multisets in
bases 2 to 8. A Python brute force over multisets
(`r3c_narcissistic.py brute`) gives the same numbers for bases 3 to 6. The
default search still matches `output/` for bases 2 to 30.

A `d`-digit number needs `d (b-1)^d >= b^(d-1)`. This allows up to 60 digits
in base 10, 69 in base 11 and 87 in base 13. The engine handles 62 digits.
So `r3c_narcissistic.py search` covers every length in bases 3 to 10, the
lengths up to 62 in bases 11 to 13, and up to 50 in base 14 (data
`r3c_narcissistic_search.txt`). Bases 3 to 13 took a few minutes on 3
threads. In base 14 one length near 50 took about a minute, so I stopped
there.

The counts with at least 2 digits are 3, 8, 13, 25, 53, 55, 50, 79, 124, 76,
189 for bases 3 to 13, and 85 up to 50 digits in base 14. They agree with
the OEIS lists of narcissistic numbers per base (A010344 for base 4 up to
A161950 for base 13, A005188 for base 10): each list holds our count plus
the `b - 1` one-digit numbers. So bases 11 to 13 have no narcissistic
number with more than 62 digits. A161951 (base 14) has 90 multi-digit terms,
5 more than our 85, and they have more than 50 digits. A note on the
question: A010353 is the list for base 9, not a table of counts.

### 58.2 The prediction (heuristic)

The refined model of chapter 5 applies with the weights `x^d`. It samples
digit multisets of a random `d`-digit number and counts those whose sum
`F` has `d` digits (basic model). The refined model also asks for the
digit-sum identity `sum (x^d - x) == 0 (mod b-1)` and multiplies by `b - 1`.
The ratio refined / basic is the factor that the residues of `x^d` give at
this length. Two cases are exact (proven):

- `x^d == x (mod 2)` for every `x` and `d >= 1`. In an odd base, `b - 1` is
  even, and the identity holds modulo 2 for free. The factor is at least 2.
- If `x^d == x (mod b-1)` for every digit `x`, the identity holds for every
  multiset, and the factor is `b - 1`. This happens for example when `b - 1`
  is squarefree and `d == 1 (mod lambda(b-1))`: every `d` in base 3, every
  odd `d` in bases 4 and 7, and `d = 13, 25, 37, 49` in base 14. It is the forced-residue experiment of section
  17.2, now in data that nobody tuned.

`r3c_narcissistic.py model` samples 400,000 multisets per cell (data
`r3c_narcissistic_model.txt`). The sampling error is below 2% of each cell.

### 58.3 The comparison (computed against heuristic)

Per base, all lengths searched (`r3c_narcissistic_compare.txt`):

| base | lengths | observed | basic model | refined model |
|---:|---:|---:|---:|---:|
| 3 | 2-7 | 3 | 2.27 | 4.54 |
| 4 | 2-13 | 8 | 4.65 | 9.15 |
| 5 | 2-20 | 13 | 7.58 | 15.56 |
| 6 | 2-28 | 25 | 10.78 | 21.97 |
| 7 | 2-35 | 53 | 14.42 | 57.72 |
| 8 | 2-43 | 55 | 18.43 | 36.14 |
| 9 | 2-52 | 50 | 22.26 | 45.27 |
| 10 | 2-60 | 79 | 26.47 | 53.32 |
| 11 | 2-62 | 124 | 30.69 | 121.41 |
| 12 | 2-62 | 76 | 35.18 | 67.16 |
| 13 | 2-62 | 189 | 39.80 | 159.64 |
| 14 | 2-50 | 85 | 40.02 | 79.43 |
| all | | 760 | 252.53 | 671.30 |

The basic model is off by a factor of 3. The refined model, which only adds
the residues, follows the bases from 3 to 189 solutions: base 7 has 53
against 57.7 and base 11 has 124 against 121.4, where the basic model says
14 and 31. The model also says what is missing. For bases 11 to 13 it
expects 0.02 solutions above 62 digits, and OEIS has none. For base 14
above 50 digits it expects 6.0, and OEIS has 5.

By the factor of the cell (cells where the basic model expects at least
0.001):

| factor refined / basic | cells | observed | basic | refined |
|---|---:|---:|---:|---:|
| below 0.9 | 7 | 1 | 2.68 | 2.20 |
| 0.9 to 1.5 | 157 | 130 | 103.62 | 105.58 |
| 1.5 to 2.5 | 136 | 163 | 79.78 | 158.96 |
| 2.5 to 5 | 26 | 81 | 16.00 | 48.85 |
| 5 and up | 30 | 139 | 19.67 | 118.86 |
| `x^d == x (mod b-1)` for all `x` | 55 | 246 | 30.77 | 236.84 |

By length and base:

| cells | count | observed | basic | refined |
|---|---:|---:|---:|---:|
| `d <= 5` | 48 | 126 | 34.17 | 83.31 |
| `d >= 6` | 434 | 634 | 218.36 | 587.99 |
| `d >= 6`, odd `b` | 208 | 354 | 100.39 | 349.72 |
| `d >= 6`, even `b` | 226 | 280 | 117.97 | 238.27 |
| `d >= 6`, `x^d == x (mod b-1)` for all `x` | 57 | 207 | 24.26 | 208.48 |
| `d >= 6`, other cells | 377 | 427 | 194.10 | 379.52 |

What this shows:

- The forced cells are the sharpest test. With `d >= 6` they hold 207
  numbers, against 208.5 from the refined model and 24.3 from the basic one.
  An example: base 14 with `d = 49` has 13 numbers, the model expects 9.0
  with a factor of exactly 13, and the basic model 0.69.
- Odd bases with `d >= 6`: 354 against 349.7. The parity factor holds.
- Long lengths, `d >= 6`: 634 against 588, a ratio of 1.08 (P = 0.03 for at
  least 634 under a Poisson law). Even bases carry the excess: 280 against
  238 (P = 0.005), mostly bases 8 and 10 (43 against 32.2 and 69 against
  47.0 for `d >= 6`).
- Short lengths, `d <= 5`: 126 against 83, a ratio of 1.5. The short
  Munchausen numbers show the same excess, and section 11.4 explains it by
  local factors, which the per-base model leaves out.
- The cells scatter a little more than Poisson draws:
  `sum (N - E)^2 / E` is 405 over the 336 long cells with `E >= 0.05`.

Answer to question 58: yes. The refined model predicts narcissistic numbers
per base and per length, with no parameter fitted to them. Its residue
factor, which reaches `b - 1 = 13` in some cells, is confirmed to a few
percent. The deviations are the short lengths, as for `x^x`, and an excess
of about 20% in the even bases, which comes mostly from bases 8 and 10.

## 57. The factorion shortfall in a narrower offset class

### 57.1 The run (computed)

`r3c_factorion_offsets.py` counts the solutions of `n = F(n) + D` with the
weights `x!`, for `D = j b (b-1)`, `j = 1` to 30, in the odd bases 15 to 35.
As in section 17.4, it counts the bulk only: numbers with at least `ref - 5`
digits, where `ref` is the number of digits of `(b-1)!`. These offsets keep
`n mod (b-1)` and `n mod b`, so they also keep the last digit of `n`. The
run took 27 minutes on 3 threads (data `r3c_factorion_offsets.txt`,
tables `r3c_factorion_offsets_report.txt`).

### 57.2 The result (computed against heuristic)

Totals over the 11 odd bases from 15 to 35:

| convention | `D = 0` | refined model | mean per offset, `D = j b (b-1)` | mean per offset, `D = j (b-1)` (section 17.4) |
|---|---:|---:|---:|---:|
| `w(0) = 0` | 3 | 11.95 | 10.83 | 11.83 |
| `w(0) = 1` | 4 | 11.76 | 10.60 | 11.10 |

The 30 narrow offsets give totals from 4 to 17 under `w(0) = 0` (median 11)
and from 6 to 17 under `w(0) = 1` (median 11). None of them is as low as
`D = 0`. With the narrow mean, a Poisson count of at most 3 has probability
0.006, and at most 4 has probability 0.020. Per base, the narrow offsets
scatter around the model as the wide ones do: the per-offset means range
from 0.43 to 1.43 per base and convention, against model values of 1.00 to
1.20.

### 57.3 What this means

The narrow class has the normal number of near-factorions: 0.91 times the
model, against 0.94 to 0.99 for the wide class. So the coincidences that
keep the last digit of `n` happen at the normal rate. The last digit is not
the cause of the shortfall at `D = 0`. That rules out the mechanism that
`analysis/wgt_lowdigits.py` tried to model, from a second direction.

In the dichotomy of the question, the shortfall is therefore chance. The
size of the chance has not changed: 3 and 4 against about 11, P = 0.006 and
0.02 per convention, with 30 of 30 offsets above `D = 0` in both. The two
conventions share their zero-free solutions, so these are not independent.
Section 17.4 already noted that about 16 groups were looked at before this
one, which turns 0.006 into about 0.1. I do not see a property of the exact
equation `n = F(n)` that the offsets lack. So I would close question 41 as
"a fluctuation of about 2.5 standard deviations", with fresh bases as the
only test left. Bases 43 and 45 (section 17.4) fit both readings.

## 49. A defect spectrum for short strings

### 49.1 The runs (computed)

`kdigit --offset D` finds every pair `(s, b)` with `b > max(s)` and
`P_s(b) - F(s) = D`: it adds `D` to the residue that the last digit needs,
and solves `P_s(b) = F(s) + D` exactly. For `D >= 0` it is complete for the
same bases as without the offset. `r3c_offsets.py` runs it for two classes
of 200 offsets each:

- `D = j`, `j = 1` to 200. These change the local factors from one offset to
  the next, so they test the factors themselves.
- `D = j L` with `L = 2^4 * 3^3 * 5^2 * 7 = 75600`, `j = 1` to 200. These keep
  `Q_s mod 16, 27, 25, 7`, so they keep the main local factors of `D = 0`.

`k = 4` uses digits up to `M = 150`, `k = 5` digits up to 60 (data
`r3c_offsets_k<k>_j.txt` and `_jL.txt`). A run takes 1.4 s for `k = 4` and
about 8 to 16 s for `k = 5` on 4 threads at load average 30 to 40.
`r3c_root_spectrum.py` computes the root heuristic for every offset, over
the strings with digits up to 22 (`k = 4`) and 11 (`k = 5`) as in section
11.4. `r3c_spectrum_report.py` compares them (`r3c_spectrum_report_k<k>.txt`).

Two remarks before the numbers.

Algebraic families (proven). Some offsets have solutions for a structural
reason, which the heuristic cannot see. Two examples under `0^0 = 1`:

- `(1, 0, 0, x)` with `x^x` a cube, that is `3 | x` or `x` a cube. In base
  `b = x^(x/3)`, `P = b^3 + x` and `F = x^x + 3`, so `D = x - 3`. This gives
  `(1,0,0,6)` in base 36 at `D = 3` and `(1,0,0,24)` in base `24^8` at
  `D = 21`.
- `(1, 3, 3, x)` with `x^x` a cube. In base `b = x^(x/3) - 1`,
  `P = (b+1)^3 + x - 1` and `F = x^x + 55`, so `D = x - 56`. This gives
  `(1,3,3,57)` at `D = 1`, `(1,3,3,60)` at `D = 4`, `(1,3,3,64)` at `D = 8`,
and so on.

The self-paying digits of chapter 2 give more: 7 in base 49 (`7 * 49^3 =
7^7`) and 8 in base 128 (`8 * 128^3 = 8^8`) pay for themselves, and any
lower digits that make up `D` complete a solution. Such families need
`D` near a weight difference, so they occur for small `D` and not for
`D = j L`. Most of them sit in bases of 100 and more, where the heuristic
expects almost nothing. So for `D = j` the comparison uses bases below 100,
and the rest is counted apart. For `D = j L` it uses all bases.

Neighbours. A small offset also catches near neighbours of the true
solutions. 3435 = `(3,4,3,5)` in base 10 has neighbours `(3,4,1,5)` at
`D = 6`, `(3,4,2,5)` at `D = 13` and `(3,4,5,x)` at `D = 18` and 40 to 42.
So the offsets `D = j` are not independent of `D = 0`. The offsets `D = j L`
are too far away for this.

### 49.2 Four-digit strings (computed against heuristic)

Under `0^0 = 1`, digits up to 22 (observed pairs `(s, b)` against the sums
of the heuristic weights over the same offsets):

| offsets | bases | observed | mean per offset | variance / mean | spacing only | primes | p-adic |
|---|---|---:|---:|---:|---:|---:|---:|
| `D = j`, 200 | below 10 | 556 | | | | 601.2 | 558.4 |
| `D = j`, 200 | 10 to 99 | 126 | | | | 129.8 | 118.6 |
| `D = j`, 200 | below 100 | 682 | 3.41 | 0.97 | 525 (all bases) | 731.0 | 677.1 |
| `D = j`, 200 | 100 and up | 16 | | | | 1.75 | 1.82 |
| `D = j L`, 200 | all | 10 | 0.05 | | 7.3 | 9.79 | 11.27 |
| `D = 0` | all | 2 | | | 1.38 | 1.39 | 0.75 |

The 16 pairs of `D = j` in bases of 100 and more are the algebraic
families of section 49.1, against 1.8 expected for chance. In bases below
100 the observed count is 0.93 times the prediction with primes and 1.01
times the p-adic one. The spacing alone, without local factors, predicts
525 for all bases, a quarter too few. The parity of `D` is a test of the 2-adic factor: for even
`j`, 373 observed against 414 (primes) and 377 (p-adic); for odd `j`, 309
against 317 and 300. The counts per offset are Poisson draws around their
own predictions: `sum (N_D - c E_D)^2 / (c E_D)` is 81 (primes) and 92
(p-adic) over the 200 offsets, below the 200 of pure Poisson noise, because
the predictions follow most of the variation from offset to offset.

The offsets `D = j L` force larger bases (`P_s(b) >= D`), 44 to 353 here, so
the counts are small: 10 against 9.8 and 11.3.

Under `0^0 = 0` the offsets `D = j` say nothing new. A string with `z` zeros
has `F_0 = F_1 - z`, so it is a solution at `D` under `0^0 = 0` exactly when
it is one at `D - z` under `0^0 = 1` (proven). Over 200 consecutive
offsets the two conventions see almost the same set: 682 pairs in both. For
`D = j L` the shift leaves the class, and the counts are 14 against 13.6
(primes) and 18.2 (p-adic).

`D = 0` against the calibrated heuristic. The factor `c` = observed /
predicted from the offsets scales the prediction for `D = 0`:

| convention | calibrated by | primes: expected at `D = 0` | P(at least observed) | p-adic: expected | P | observed |
|---|---|---:|---:|---:|---:|---:|
| `0^0 = 1` | `D = j` | 1.29 | 0.37 | 0.74 | 0.17 | 2 |
| `0^0 = 1` | `D = j L` | 1.44 | 0.42 | 0.63 | 0.13 | 2 |
| `0^0 = 0`, bases below 100 | `D = j` | 2.41 | 0.10 | 2.11 | 0.06 | 5 |
| `0^0 = 0`, bases below 100 | `D = j L` | 2.81 | 0.15 | 1.76 | 0.03 | 5 |

Two of the 5 solutions of `D = 0` under `0^0 = 0` in bases below 100 are
the self-paying `(7,0,0,0)` and `(7,0,0,1)` in base 49. The other 3 fit both
versions. `D = 0` also has 13 solutions in bases of 100 and more, all from
self-paying digits, against 0.01 for chance.

### 49.3 Five-digit strings (computed against heuristic)

SPEC5

### 49.4 Answer to question 49

ANSWER49

## 48. p-adic local factors in the root heuristic

### 48.1 The factor (proven)

Section 11.4 gives a string `s` the weight `min(1, S / P_s'(b*))`, where
`b*` is the real root of `P_s(b) = F(s)` and `S = prod_p rho_s(p)` over the
primes up to 31. Here `rho_s(p)` is the number of roots of `Q_s` modulo `p`.

The right local factor at `p` is the density of the event `p^e | Q_s(b)`
for a random integer `b`, divided by the chance `p^(-e)` for a random value,
in the limit of large `e`. That is the number `N_s(p^e)` of roots of `Q_s`
modulo `p^e`, not `N_s(p^e) / p^(e-1)` as the question writes. Facts:

- If every root of `Q_s` mod `p` is simple (`Q_s'(r) != 0 mod p`), each
  lifts to exactly one root mod `p^e` (Hensel), and `N_s(p^e) = rho_s(p)`.
- A multiple root mod `p` can lift to no root, or to several. So
  `N_s(p^e)` can be 0 where `rho_s(p) = 2`, and it can grow with `e` near a
  root that is multiple in `Z_p`.
- Over a constant term that is uniform mod `p^e`, `N_s(p^e)` averages
  exactly 1, for every `e`: each of the `p^e` residues `r` is a root for
  exactly one constant term. So the new factor is unbiased in the same sense
  as the old one.

`r3c_root_spectrum.py` computes both versions. The "p-adic" version uses
`N_s(64)`, `N_s(81)` and `N_s(125)` in place of `rho_s(2)`, `rho_s(3)` and
`rho_s(5)`, and keeps `rho_s(p)` for `p = 7` to 31. It reproduces the
numbers of section 11.4 for the old version exactly.

### 48.2 The table of section 11.4, redone (heuristic)

Expected number of solutions under `0^0 = 1`, against the 6, 2 and 6 observed
(digits up to `X`, as in section 11.4):

| length | digits up to | spacing only | primes (11.4) | p-adic, 16, 27, 25 | p-adic, 64, 81, 125 | p-adic, 128, 81, 125 | p-adic, 32, 243, 125 | observed |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 60 | 2.31 | 5.09 | 5.59 | 5.59 | 5.59 | 5.59 | 6 |
| 4 | 22 | 1.38 | 1.39 | 0.79 | 0.75 | 0.74 | 0.74 | 2 |
| 5 | 11 | 1.13 | 2.42 | 3.44 | 3.32 | 3.34 | 3.34 | 6 |
| all | | 4.82 | 8.90 | 9.82 | 9.66 | 9.67 | 9.67 | 14 |

The p-adic factor is stable once `e` reaches 4, 3 and 2 for the primes 2, 3
and 5. It moves the 5-digit prediction from 2.42 to 3.32, so 6 observed is
no longer unusual (P(at least 6) = 0.12 against 0.037). It moves the
4-digit prediction down, from 1.39 to 0.75 (P(at least 2) = 0.17 against
0.41). The total moves from 8.90 to 9.66 against 14 observed.

Most of the change comes from the observed solutions themselves, because
their weights are near the cap of 1. For example 3435 = `(3,4,3,5)` in base
10 has `rho(2) = 2` but only one root mod 64 (`N(64) = 1`), so its weight
drops from 1 (capped) to 0.49. `(2,2,3,5,2)` in base 6 has `rho(5) = 1` but
`N(125) = 10`. With 2 to 6 solutions per length, such single strings decide
the comparison. Section 49 replaces them by hundreds of offsets.

### 48.3 The test with the offsets (computed against heuristic)

CALIB48

SECTIONS
