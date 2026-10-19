# 7. Conjectures and open problems

Each entry states what is known and what the evidence is. "Proven" means a
proof in this library. "Computed" means an exhaustive search. "Model" means
the probabilistic model of chapter 5. Chapter 8 settles some of these problems
and explains which barrier blocks each of the others; its section 8.7 has a
status table.

## 7.1 Solutions with `b` digits

Conjecture (original). For `b > 2` no base has a `b`-digit solution.

- Under `0^0 = 0` it is false: base 15 has `(1,2,4,3,14,14,13,3,4,1,9,1,1,0,14)`
  and base 16 has `(1,2,3,11,2,3,0,9,15,15,5,7,2,15,6,11)` (computed).
- Under `0^0 = 1` it holds for bases 3 to 45 (computed; bases 42, 44 and 45
  only for `b`-digit numbers, section 8.6).
- For `b >= 7`, a `b`-digit solution contains the digit `b-1` at least three
  times (proven, Proposition 1.6). Both counterexamples contain it exactly
  three times.
- The model expects a `b`-digit solution in about 8% of large bases. Bases 3 to
  45 have none under `0^0 = 1`. The basic model expects 3.2 there and the
  refined model 3.6, so none happens with probability 0.04 or 0.03. Section
  11.2 shows that the model overestimates this length at these bases, by about
  1.6x. With that correction, none is an ordinary outcome. I expect the
  conjecture to fail under `0^0 = 1` too.

## 7.2 Finitely many short solutions under `0^0 = 1` (refuted)

Conjecture (refuted). Under `0^0 = 1`, for each `k >= 3`, only finitely many
bases have a `k`-digit solution.

Chapter 22 refutes it: the binomial families give infinitely many solutions of
every length `k >= 3`, in bases from about `10^108942` up (Corollary 22.7).
The evidence below still holds in its ranges. The open question is now whether
every solution beyond some size belongs to such a family (question 64).

- For `k = 2` there are infinitely many (proven, section 2.4).
- Under `0^0 = 0` there are infinitely many for every `k` (proven,
  Proposition 2.7).
- In every base up to `10^51.5` there are exactly 6 three-digit solutions; up
  to `10^18.6` exactly 2 four-digit solutions; up to `10^8.5` exactly 6
  five-digit solutions; up to `10^4.6` exactly 1 six-digit solution
  (computed, section 3.2).
- A heuristic count of integer roots gives a finite expectation for every
  `k >= 3` (section 3.5).
- Proven when one digit is large and lies in its square class, with an
  explicit bound, when that digit leads (Theorem 8.3). Corollary 8.4, for a
  large digit in another place, missed the binomial families (section 22.3.3).
  The remaining cases are
  Pell-type equations with a prescribed coordinate, beyond current methods
  (section 8.2).

## 7.3 Lengths without solutions

Conjecture (refuted as stated). Under `0^0 = 1` no base has a solution with
9 digits. The same holds for 18, 21, 22, 24, 26 and 28 digits.

The binomial families of chapter 22 give solutions of every length, these
included, in astronomically large bases (Corollary 22.7). What survives is the
statement for bases near the length, where the evidence below applies: no
9-digit solution in bases up to 100,000.

- No base up to 100,000 has a 9-digit solution, and no base up to 10,000 has
  one with the other lengths (computed, section 3.4).
- In larger bases the model makes them very unlikely: a 9-digit solution in
  base 128 or above has probability below `10^-8` (section 3.4).
- The model predicts that about 37% of long lengths are missing under
  `0^0 = 1`. Under `0^0 = 0` no length is missing (proven).
- A proof meets the same barrier as section 7.2 (section 8.2).

## 7.4 How many solutions per base

- Is `N_1(b)` bounded? Unknown. `N_0(b)` is unbounded (proven,
  Proposition 4.2).
- Average count: the model predicts that the average of `N_0(b)` over many
  bases tends to 1.5 and the average of `N_1(b)` to about 1.07. In the model,
  the count in one base follows a Poisson law. The families of chapter 2 make
  the tails heavier.
- Are there infinitely many bases without solutions? The model says that
  about 17% of even and 8% of odd bases near base 40 have none under either
  convention (section 9.7), and 20% and 9% in the large-base limit (section
  4.5). Bases 19, 27 and 35
  are the empty ones up to 41. Section 8.5 explains why no uniform method is
  available. No even base from 10 to 41 is empty, against 2.6 expected
  (probability 0.06), and base 44 has a solution.
- How far apart are the bases with many solutions? Base `n^(n-1)` has at least
  `2^(n-1) - 2` solutions under `0^0 = 0`, and the bases with `c` self-paying
  digits are powers `r^t` with `t >= c + 1`, at most
  `X^(1/(c+1)) (1 + o(1))` of them up to `X` (section 9.8).
- For `N_1(b)`, self-paying digits only help together with near-solutions of
  small defect (Proposition 8.6).

## 7.5 Unexplained observations

- The empty bases 19, 27 and 35 are all `== 3 (mod 8)`. Three of the four such
  bases from 11 to 35 are empty. Resolved: base 43, the next one, has a
  solution (computed), so the pattern was chance.
- Under `0^0 = 1`, `(b-1)`-digit solutions are about 1.6 times as common as the
  refined model predicts in bases 10 to 38. Correlation tests found nothing,
  and after allowing for how the group was chosen the excess is consistent with
  chance. In the fresh bases 39 to 43 the excess continues weakly: 5 observed
  against 2.45 expected, probability 0.10 (section 5.5). Resolved: over all
  lengths from `b-6` to `b` the counts fit the model (section 9.6).

## 7.6 Structure

- Under `0^0 = 1`, is there an infinite family of solutions with 3 or more
  digits? Answered: yes. The binomial families give infinitely many
  solutions of every length `k >= 3` (Theorem 22.6, Corollary 22.7).
  Theorem 25.5 gives a second family, `(c^j, 0, ..., 0, x)`, for every
  length `k >= 4`. Its zeros weigh 1 each, and the last digit pays for them.
  All these members lie in astronomically large bases. Theorem 8.3 rules
  out families with a large leading digit in the square class, and in every
  power identity the large digit is the last digit (Theorem 25.2). Under
  `0^0 = 1` the only solutions made of zero-balance placements alone are
  `(a, 1)` (section 8.3).
- Can every solution under `0^0 = 1` be explained as a coincidence, apart from
  the self-paying digits, swaps, 2-digit families and the identity families
  above? The catalog of chapter 3 has no structured example beyond these.
  Section 15.5 explains one more: the 11-digit solution of base 64 is a
  chain of power identities plus the self-paying digits 4 and 16. That
  construction gave no other solution beyond `(a, 1)` in bases `r^t` with
  `r <= 40` and `t <= 300`.
- Do Munchausen numbers have a general form? The known families are those of
  chapter 2, the binomial families of chapter 22, the family of Theorem 25.5
  and the chains of section 15.5. Conjecture 25.8 says that, for each length
  `k >= 3`, all but finitely many solutions under `0^0 = 1` belong to the
  two linear identity families (question 64). The solutions near `b` digits
  show no structure.

## 7.7 Complexity

- Is there an exact search whose cost grows more slowly than `1.87^b`? A search
  restricted to typical multisets grows about 1.6x per base, but it is not
  exact. Chapter 9 turns this into a search with a measured miss rate, and
  conjectures that any fixed miss rate allows the typical growth rate
  (Conjecture 9.1). Chapter 10 shows that in the model no tree search can do
  better than about `1.638^b`, and that the exact tree grows like `2^b`. Chapter 6 explains why I do not expect a polynomial method.
- Section 8.1 shows that a proof either way is out of reach: an unconditional
  lower bound would prove P != NP, and NP-hardness would prove P = NP.
- Can the number of solutions in a base be predicted exactly without a
  search? Only on average, through the model.
