# Open research questions

A reading of chapters 1 to 12 produced these 30 questions. Each gives the
question, why it matters, a first attack, a size and a priority (1 = first).
Agents and readers that answer one should record the answer in the chapter
it belongs to and mark it here. Quick-check scripts by the questioner are in
`analysis/questioner/`; their numbers are leads, not results.

## Theme I. The polynomial Q_s as an algebraic object

1. Is the base-904 solution an Aurifeuillian factorization? `(1,x,1)` under
   `0^0 = 1` (and `(1,x,0)` under `0^0 = 0`) is a solution exactly when
   `b (b + x) = x^x + 1`, so it needs a divisor of `x^x + 1` within `x` of its
   square root. For squarefree `x == 3 (mod 4)`, `Phi_2x(x)` splits into
   Aurifeuillian factors `L < M`. For x = 3, `Phi_6(3) = 1 * 7` with `b = 4`.
   For x = 7, `Phi_14(7) = 113 * 911` with `b = 904 = 8 * 113`. For such `x`
   from 7 to 79, `M / L` stays between 6.98 and 8.06, near `e^2`.
   - Tasks: prove the limit or bounds of `M / L`; say for every short
     solution which identity, if any, produces its factor pair; search only
     algebraic factorizations of `x^x + c`, which allows two large digits.
   - Why: it would make `(1,7,1)` in base 904 structural. `(6,1,5)` in base 91
     is a counterexample candidate. Small to medium. Priority 1.

2. When is `Q_s` reducible, and can a string pass every local test without a
   rational root? For k = 5, digits up to 7, `0^0 = 1`, 28,615 of 28,672 are
   irreducible: 39 split 1+3, 17 split 2+2, 1 splits 1+1+2.
   - Examples: `(1,2,1,0,2)` gives `(r^2+r-3)(r^2+r+3)`, from a decomposable
     digit polynomial; `(1,0,0,0,4)` gives `r^4 - 256`.
   - Conjecture: for large `F(s)` reducibility comes only from a rational
     root, a decomposition `P_s = G(h(r))`, or `Q_s` close to
     `s_1 (r^(k-1) - Z^(k-1))`.
   - Then prove that no `Q_s` is intersective (a root mod every n but no
     rational root), or find one.
   - Literature: Fried, Ritt, Bilu-Tichy, Capelli, Berend-Bilu. Priority 1.

3. Roots as a function of one varying digit: the near-integer law. Fix all
   digits but `x` and let `b*(x)` be the real root.
   - Square class: does the fractional part of `b*(x)` concentrate at rational
     points?
   - Outside it: is it equidistributed, with records of `||b*(x)||` scaling
     like `1/X`?
   - State the cleanest near-integer problem, such as how close
     `sqrt(x) x^((x-2)/2)` comes to an integer. Medium. Priority 2.

4. Small Galois groups and integral points. The discriminant of `P_s(r) - N`
   is a polynomial in `N`. For k = 4 a smaller group needs a square; for k = 5,
   a point on `y^2 = cubic(N)`. Count non-decomposable strings with a smaller
   group, and ask whether `N = F(s)` hits integral points (Siegel, Baker).
   Medium. Priority 3.

## Theme II. Other inputs to the polynomial

5. A model for negative bases. In base `-b`, `n == digit sum (mod b+1)`, and
   the analog of Proposition 10.2 should make `b+1` the only such modulus.
   Predictions: the parity doubling under `0^0 = 0` moves to odd `b`; lengths
   are odd and at most `b+1`. Derive the length shares and the expected count
   per base, and compare with a census up to `b` = 16 to 18. Are -3, -6, -9
   empty by chance? Small to medium. Priority 1.

6. A negative-base search engine. Fixed prefixes still form intervals in
   negabase. Adapt `fast search` and run bases up to about 35. Large.
   Priority 2.

7. Gaussian bases. Count Munchausen numbers in the bases `-n+i` (digits 0 to
   `n^2`). Leads: base -1+i has 6 under `0^0 = 0` and 1 under `0^0 = 1` up to
   length 20; base -2+i has `(4,2,4,0,4,1,0,4)` under `0^0 = 0`. A 3-digit
   `Q_s` never has nonreal roots. Imaginary bases `ci` reduce to base `-c^2`.
   Census for n = 1 to 3 or 4, a length bound and a model. Medium. Priority 2.

8. Partners beyond length 3. Is there a 3-digit negative-base solution that is
   not a partner (Proposition 12.3), apart from `(1,1,1)`? For k >= 5, is any
   string a solution in both a base `b` and a base `-c`? Small. Priority 3.

9. The convention `0^0 = m` as a free integer. For `m` other than 0 and 1
   there are no twins or self-paying families. Predictions: in odd bases the
   parity factor is 2 for even `m` and `1 + e^(-2)` for odd `m`. Measure
   `N_m(b)` for m in {-2, -1, 2, 3}, bases 10 to 30. Needs question 26.
   Priority 3.

10. Universality. Replace `x^x` by `x^(x+t)` or by `x!` (factorions, OEIS
    A193163, A014080). Are the length shares 8/55/23% and the Poisson law
    universal for weights of this size? Medium. Priority 2.

11. Rational roots and rational bases. Count strings with a rational root
    `p/q > max(s)`, `q > 1`, for k = 3 and 4. Is there a meaningful version in
    the Akiyama-Frougny-Sakarovitch rational number systems? Small.
    Priority 3.

## Theme III. Nonexistence and finiteness

12. Prove that `b (b + x) = x^x + 1` has only the solutions x = 3 and x = 7.
    Even `x` is in the square class. For odd prime `x`, the prime factors of
    `Phi_2x(x)` are `1 (mod 2x)`. Combine with coverings and the Pell form
    `U^2 - 4x Y^2 = x^2 + 4`, `Y = x^((x-1)/2)`. Literature: primitive
    divisors (Bilu-Hanrot-Voutier), S-unit values of recurrences. Large.
    Priority 2.

13. Prove that only base 3 has two 2-digit solutions under `0^0 = 1` (true up
    to `10^54`). The condition `a'(a^a + c^c - c) = a(a'^a' + c'^c' - c')`
    forces near cancellation; p-adic valuations should finish it. Medium.
    Priority 2.

14. Coverings beyond parity. Find an infinite family of strings, with one or
    two varying digits, that is never a solution for a reason other than the
    congruences of section 1.6, or prove that every covering reduces to them.
    Use prime powers, k = 4 and 5, two parameters, both conventions. Medium.
    Priority 2.

15. Constructions under `0^0 = 1` from power identities: self-paying digits,
    swaps, chains, and digits that pay for zeros, like
    `(16,0,0,0,0,0,1,0,0,4,8)` in base 64. Are there finitely many? Could they
    give a base with `N_1(b) >= 6`? Medium. Priority 2.

16. Finitely many primitive cores under `0^0 = 0`? In particular, finitely many
    perfect-power 2-digit bases with a self-paying digit on top, like
    `(8,0,2,4)` in base 128, that is, `(a^a + c^c - c)/a = r^t` with
    `t | s(r^s - 1)`: a Pillai-type problem. Small to medium. Priority 2.

17. The missing `b`-digit solution under `0^0 = 1`. Bases 3 to 45 have none
    against about 3.2 expected (P about 0.04). Is there a suppression
    mechanism for this shape (leading digit 1, 3 to 5 copies of `b-1`)? Check
    the parity of zeros and the residue mod `b-1` against the exact finite-`b`
    model. Then hunt with `--min-digits b --zscore 3` in bases 46 to 52.
    Analysis priority 1, search priority 2.

18. Missing lengths 31 to 45 in bases up to 127, against the predicted 37%.
    Large. Priority 3.

## Theme IV. The model, probability and dynamics

19. A sharp test of the model: force `w'(x) == x (mod b-1)` in perturbed
    weights. The refined model then predicts about `b-1` times as many
    solutions. Forcing `w'(x) == x + 1 (mod b-1)` should leave only
    `(b-1)`-digit solutions, about `0.55 (b-1)` per base. Bases 12 to 24.
    Needs a `--set-residue` option. Priority 1.

20. Cycle census of `n -> F(n)`. Count cycles of each length `L` on digit
    multisets for b = 3 to 16. Random mappings predict Poisson(`1/L`); in odd
    bases under `0^0 = 0`, `F(n) == n (mod 2)` predicts `2/L`. Lead: 2-cycles
    in every odd base 3 to 11 under `0^0 = 0`, none in even bases 4 to 10.
    Priority 1.

21. The length law from near-solutions: use the lengths of the offset
    solutions of section 11.1 to test the `e^(-J)` law and the bump at
    `J > ln b + 1` with thousands of near-solutions. Priority 2.

22. A Chen-Stein Poisson theorem in the model, with twins and shared
    solutions; predict the correlation 0.56 of `N_0` and `N_1`. Priority 3.

23. Empty even bases: run `--zscore 3` on bases 46, 48, 50. Large.
    Priority 2.

24. Regress the per-base means `lambda_m(b)` of the defect spectrum on
    `b mod 3, 4, 8`, `omega(b-1)` and perfect powers. Small. Priority 3.

## Theme V. Search algorithms and complexity

25. The defect spectrum in one pass: widen the interval by `W` and check every
    `|D| <= W` at the leaves. Priority 2.

26. A general weight table in the engine: `w(0) = m`, `x^(x+t)`, `x!`, forced
    residues. Pruning needs only increasing weights. Unblocks 9, 10, 19.
    Priority 1.

27. With `b` in unary and arbitrary binary weights, is "some `n` equals the sum
    of the weights of its digits" NP-complete? Unlike `L_m` this is not a
    tally language. Priority 3.

28. Why the sieve passes 2 to 4 times more strings than the product of
    derangement shares: for k = 3 with digits up to 80, 46 pass against about
    2 expected. Small primes, leading digits, square discriminants. Priority 3.

29. Where tree search and `kdigit` cross over for lengths 8 to 12; push those
    lengths to bases `10^4` to `10^5`. Priority 3.

## Theme VI. Erdos-style

30. Integers that are Munchausen in several bases. Under `0^0 = 0`,
    `7^7 + 1 = 823544` is a solution in five bases (49, 343, 904, 117649,
    823537). Under `0^0 = 1` all 201 integers with two bases in the catalog are
    2-digit pairs. Is there one with a representation of 3 or more digits? What
    is the most bases one integer can have under `0^0 = 1`? Priority 3.
