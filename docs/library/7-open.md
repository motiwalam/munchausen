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
- Under `0^0 = 1` it holds for bases 3 to 43 (computed; base 42 only for
  `b`-digit numbers).
- For `b >= 7`, a `b`-digit solution contains the digit `b-1` at least three
  times (proven, Proposition 1.6). Both counterexamples contain it exactly
  three times.
- The model expects a `b`-digit solution in about 8% of large bases. Bases 3 to
  41 have none under `0^0 = 1`, against 2.9 expected, which happens about 5% of
  the time under the model. I expect the conjecture to fail under `0^0 = 1`
  too.

## 7.2 Finitely many short solutions under `0^0 = 1`

Conjecture. Under `0^0 = 1`, for each `k >= 3`, only finitely many bases have
a `k`-digit solution.

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
  explicit bound (Theorem 8.3, Corollary 8.4). The remaining cases are
  Pell-type equations with a prescribed coordinate, beyond current methods
  (section 8.2).

## 7.3 Lengths without solutions

Conjecture. Under `0^0 = 1` no base has a solution with 9 digits. The same
holds for 18, 21, 22, 24, 26 and 28 digits.

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
  about 15% of bases have none under either convention. Bases 19, 27 and 35
  are the empty ones up to 41. Section 8.5 explains why no uniform method is
  available.
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
  against 2.45 expected, probability 0.10 (section 5.5). Open.

## 7.6 Structure

- Under `0^0 = 1`, is there an infinite family of solutions with 3 or more
  digits? Every known infinite family relies on zeros that weigh nothing, or
  has 2 digits. Theorem 8.3 rules out families with a large leading digit in
  the square class. Under `0^0 = 1` the only solutions made of zero-balance
  placements alone are `(a, 1)` (section 8.3).
- Can every solution under `0^0 = 1` be explained as a coincidence, apart from
  the self-paying digits, swaps and 2-digit families? The catalog of chapter 3
  has no other structured example.
- Do Munchausen numbers have a general form? Only the families of chapter 2
  are known. The solutions near `b` digits show no structure.

## 7.7 Complexity

- Is there an exact search whose cost grows more slowly than `1.87^b`? A search
  restricted to typical multisets grows about 1.6x per base, but it is not
  exact. Chapter 6 explains why I do not expect a polynomial method.
- Section 8.1 shows that a proof either way is out of reach: an unconditional
  lower bound would prove P != NP, and NP-hardness would prove P = NP.
- Can the number of solutions in a base be predicted exactly without a
  search? Only on average, through the model.
