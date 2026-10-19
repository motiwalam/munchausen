# Open research questions

A reading of chapters 1 to 12 produced these 30 questions. Each gives the
question, why it matters, a first attack, a size and a priority (1 = first).
Agents and readers that answer one should record the answer in the chapter
it belongs to and mark it here. Quick-check scripts by the questioner are in
`analysis/questioner/`; their numbers are leads, not results.

## Theme I. The polynomial Q_s as an algebraic object

1. (Answered in chapter 16: the Aurifeuillian ratio M/L tends to e^2 (Theorem 16.2), so x = 3 and 7 are the only algebraic cases.) Is the base-904 solution an Aurifeuillian factorization? `(1,x,1)` under
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

2. (Answered in chapter 16 for k <= 5; criteria for k = 6.) When is `Q_s` reducible, and can a string pass every local test without a
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

3. (Answered in section 12.5 for four families: uniform outside the square
   class, `1/(2x)` inside it.) Roots as a function of one varying digit: the
   near-integer law. Fix all
   digits but `x` and let `b*(x)` be the real root.
   - Square class: does the fractional part of `b*(x)` concentrate at rational
     points?
   - Outside it: is it equidistributed, with records of `||b*(x)||` scaling
     like `1/X`?
   - State the cleanest near-integer problem, such as how close
     `sqrt(x) x^((x-2)/2)` comes to an integer. Medium. Priority 2.

4. (Answered in chapter 16 for k = 4, 5.) Small Galois groups and integral points. The discriminant of `P_s(r) - N`
   is a polynomial in `N`. For k = 4 a smaller group needs a square; for k = 5,
   a point on `y^2 = cubic(N)`. Count non-decomposable strings with a smaller
   group, and ask whether `N = F(s)` hits integral points (Siegel, Baker).
   Medium. Priority 3.

## Theme II. Other inputs to the polynomial

5. (Answered in chapter 14: census of bases -2 to -35 fits the model.) A model for negative bases. In base `-b`, `n == digit sum (mod b+1)`, and
   the analog of Proposition 10.2 should make `b+1` the only such modulus.
   Predictions: the parity doubling under `0^0 = 0` moves to odd `b`; lengths
   are odd and at most `b+1`. Derive the length shares and the expected count
   per base, and compare with a census up to `b` = 16 to 18. Are -3, -6, -9
   empty by chance? Small to medium. Priority 1.

6. (Answered in chapter 14: fast/src/bin/worlds.rs.) A negative-base search engine. Fixed prefixes still form intervals in
   negabase. Adapt `fast search` and run bases up to about 35. Large.
   Priority 2.

7. (Answered in chapter 14 for n = 1 to 3.) Gaussian bases. Count Munchausen numbers in the bases `-n+i` (digits 0 to
   `n^2`). Leads: base -1+i has 6 under `0^0 = 0` and 1 under `0^0 = 1` up to
   length 20; base -2+i has `(4,2,4,0,4,1,0,4)` under `0^0 = 0`. A 3-digit
   `Q_s` never has nonreal roots. Imaginary bases `ci` reduce to base `-c^2`.
   Census for n = 1 to 3 or 4, a length bound and a model. Medium. Priority 2.

8. (Answered in chapter 16.) Partners beyond length 3. Is there a 3-digit negative-base solution that is
   not a partner (Proposition 12.3), apart from `(1,1,1)`? For k >= 5, is any
   string a solution in both a base `b` and a base `-c`? Small. Priority 3.

9. (Answered in chapter 17.) The convention `0^0 = m` as a free integer. For `m` other than 0 and 1
   there are no twins or self-paying families. Predictions: in odd bases the
   parity factor is 2 for even `m` and `1 + e^(-2)` for odd `m`. Measure
   `N_m(b)` for m in {-2, -1, 2, 3}, bases 10 to 30. Needs question 26.
   Priority 3.

10. (Answered in chapters 14 and 17.) Universality. Replace `x^x` by `x^(x+t)` or by `x!` (factorions, OEIS
    A193163, A014080). Are the length shares 8/55/23% and the Poisson law
    universal for weights of this size? Medium. Priority 2.

11. (Answered in chapter 16.) Rational roots and rational bases. Count strings with a rational root
    `p/q > max(s)`, `q > 1`, for k = 3 and 4. Is there a meaningful version in
    the Akiyama-Frougny-Sakarovitch rational number systems? Small.
    Priority 3.

## Theme III. Nonexistence and finiteness

12. (Partly answered in chapters 16 and 18: no solution for x up to 4e9; none for odd prime powers x >= 9 (Proposition 18.6); a further solution needs a mixed non-principal ideal (Corollary 18.11); abc implies none.) Prove that `b (b + x) = x^x + 1` has only the solutions x = 3 and x = 7.
    Even `x` is in the square class. For odd prime `x`, the prime factors of
    `Phi_2x(x)` are `1 (mod 2x)`. Combine with coverings and the Pell form
    `U^2 - 4x Y^2 = x^2 + 4`, `Y = x^((x-1)/2)`. Literature: primitive
    divisors (Bilu-Hanrot-Voutier), S-unit values of recurrences. Large.
    Priority 2.

13. (Answered in chapter 15: proven (Theorem 15.7).) Prove that only base 3 has two 2-digit solutions under `0^0 = 1` (true up
    to `10^54`). The condition `a'(a^a + c^c - c) = a(a'^a' + c'^c' - c')`
    forces near cancellation; p-adic valuations should finish it. Medium.
    Priority 2.

14. (Answered in chapter 15: coverings with moduli 3^e and 2^e exist.) Coverings beyond parity. Find an infinite family of strings, with one or
    two varying digits, that is never a solution for a reason other than the
    congruences of section 1.6, or prove that every covering reduces to them.
    Use prime powers, k = 4 and 5, two parameters, both conventions. Medium.
    Priority 2.

15. (Partly answered in chapter 15.) Constructions under `0^0 = 1` from power identities: self-paying digits,
    swaps, chains, and digits that pay for zeros, like
    `(16,0,0,0,0,0,1,0,0,4,8)` in base 64. Are there finitely many? Could they
    give a base with `N_1(b) >= 6`? Medium. Priority 2.

16. (Answered in chapter 15: no, swaps give infinitely many.) Finitely many primitive cores under `0^0 = 0`? In particular, finitely many
    perfect-power 2-digit bases with a self-paying digit on top, like
    `(8,0,2,4)` in base 128, that is, `(a^a + c^c - c)/a = r^t` with
    `t | s(r^s - 1)`: a Pillai-type problem. Small to medium. Priority 2.

17. (Answered in section 11.2: the model overestimates `b` digits by about
    1.6x at these bases because of the forced top digits; the data are
    normal.) The missing `b`-digit solution under `0^0 = 1`. Bases 3 to 45 have none
    against 3.2 expected in the basic model (P about 0.04) and 3.6 in the
    refined model (P about 0.03). Is there a suppression
    mechanism for this shape (leading digit 1, 3 to 5 copies of `b-1`)? Check
    the parity of zeros and the residue mod `b-1` against the exact finite-`b`
    model. Then hunt with `--min-digits b --zscore 3` in bases 46 to 52.
    Analysis priority 1, search priority 2.

18. Missing lengths 31 to 45 in bases up to 127, against the predicted 37%.
    Large. Priority 3.

## Theme IV. The model, probability and dynamics

19. (Answered in chapter 17: forced residues multiply the count by 18.9 against 16.9 predicted.) A sharp test of the model: force `w'(x) == x (mod b-1)` in perturbed
    weights. The refined model then predicts about `b-1` times as many
    solutions. Forcing `w'(x) == x + 1 (mod b-1)` should leave only
    `(b-1)`-digit solutions, about `0.55 (b-1)` per base. Bases 12 to 24.
    Needs a `--set-residue` option. Priority 1.

20. (Answered in chapter 15.) Cycle census of `n -> F(n)`. Count cycles of each length `L` on digit
    multisets for b = 3 to 16. Random mappings predict Poisson(`1/L`); in odd
    bases under `0^0 = 0`, `F(n) == n (mod 2)` predicts `2/L`. Lead: 2-cycles
    in every odd base 3 to 11 under `0^0 = 0`, none in even bases 4 to 10.
    Priority 1.

21. (Partly answered in section 11.2a: the law holds for small `J`, with
    large cell-by-cell deviations.) The length law from near-solutions: use the lengths of the offset
    solutions of section 11.1 to test the `e^(-J)` law and the bump at
    `J > ln b + 1` with thousands of near-solutions. Priority 2.

22. (Answered in chapter 13, part 2: proven in the
    basic coupled model with error `O(1/b)`; the refined model needs an
    assumption on residues; predicted pooled correlation 0.47, observed 0.56.)
    A Chen-Stein Poisson theorem in the model, with twins and shared
    solutions; predict the correlation 0.56 of `N_0` and `N_1`. Priority 3.

23. (Section 11.2 finds the deficit to be chance with each base's own
    spectrum.) Empty even bases: run `--zscore 3` on bases 46, 48, 50. Large.
    Priority 2.

24. (Answered in section 11.2a: no residue pattern; about 20% real spread,
    partly explained by forced top digits.) Regress the per-base means `lambda_m(b)` of the defect spectrum on
    `b mod 3, 4, 8`, `omega(b-1)` and perfect powers. Small. Priority 3.

## Theme V. Search algorithms and complexity

25. The defect spectrum in one pass: widen the interval by `W` and check every
    `|D| <= W` at the leaves. Priority 2.

26. (Answered in chapter 17: options --zero, --shift, --factorial, --set-residue.) A general weight table in the engine: `w(0) = m`, `x^(x+t)`, `x!`, forced
    residues. Pruning needs only increasing weights. Unblocks 9, 10, 19.
    Priority 1.

27. (Answered in chapter 13, part 1: NP-complete,
    also for increasing weights, and #P-complete under parsimonious
    reductions; the `x^(e(x))` variants stay open.) With `b` in unary and
    arbitrary binary weights, is "some `n` equals the sum of the weights of
    its digits" NP-complete? Unlike `L_m` this is not a tally language.
    Priority 3.

28. (Answered in section 11.5: small primes pass most strings because of the
    digit-sum identity at r = 1, and rational roots pass every prime.) Why the
    sieve passes 2 to 4 times more strings than the product of
    derangement shares: for k = 3 with digits up to 80, 46 pass against about
    2 expected. Small primes, leading digits, square discriminants. Priority 3.

29. Where tree search and `kdigit` cross over for lengths 8 to 12; push those
    lengths to bases `10^4` to `10^5`. Priority 3.

## Theme VI. Erdos-style

30. (Answered in chapter 15.) Integers that are Munchausen in several bases. Under `0^0 = 0`,
    `7^7 + 1 = 823544` is a solution in five bases (49, 343, 904, 117649,
    823537). Under `0^0 = 1` all 201 integers with two bases in the catalog are
    2-digit pairs. Is there one with a representation of 3 or more digits? What
    is the most bases one integer can have under `0^0 = 1`? Priority 3.

## Round 2: questions raised by the answers

31. (Answered in chapter 18: yes, with a twisted Ramanujan sum; M/L tends to e^(2/y) or 1 (Theorem 18.20).) Does the exact series for `M / L` (Theorem 16.2) extend to Aurifeuillian
    factors of `a^n +- b^n` in general? (chapter 16)
32. (Partly answered in chapter 18: solved for prime powers x (Theorem 18.8) and odd x <= 1001 (Theorem 18.12); none for n even; finite under abc; n = 5 open.) Is the set of solutions `(x, n)` of `b (b + x) = x^n + 1` with `n >= 4`
    finite? Only `(7, 7)` is known. (chapter 16)
33. For every `k`, is there a bound `F <= C_k M^(c_k)` beyond which every
    factorization of `Q_s` without a linear factor comes from a decomposition
    of `P_s`? (chapter 16)
34. (Answered in chapter 18: the root heuristic is symmetric in sign; in the square class small t favours positive roots about 9 to 1.) Why do negative bases lack the non-partner 3-digit solutions, such as
    `(3,1,3)`, that positive bases have? (chapters 12 and 16)
35. (Answered in chapter 23: chance; near-2-cycles have the normal rate, so no second invariant.) Even bases under `0^0 = 0` have 1 two-cycle of `n -> F(n)` against 3.5
    expected. Is there a second invariant, or is this chance? (chapter 15)
36. (Answered in chapter 18 below 10^51: only base 25.) Which bases have one 2-digit and one 3-digit solution? (chapter 15)
37. Close the case `a^a ~ c^c` of the cores in self-paying bases, where abc
    does not apply. (chapter 15)
38. Does every covering need a modulus on which `x^x - x` misses residues,
    that is a power of 2 or 3, or 25? (chapter 15)
39. (Partly answered in chapter 18: none in the ranges searched; such an integer has a rigid shape (Corollary 18.17).) Does some integer have three bases under `0^0 = 1`? (chapter 15)
40. (Partly answered in chapter 18: still open; gadgets made of pure powers need superpolynomial exponents (Corollary 18.23).) Is the problem with weights `x^(e(x))`, `e` in unary, NP-hard? It sits
    between the NP-complete general problem and the real one. (chapter 13)
41. (Answered in chapters 19 and 23: offsets that keep every small residue have the normal count, so the shortfall is most likely chance, P about 0.05; base 49 not yet searched.) Long factorions are rare in odd bases: bases 14 to 36 have 3 against 11.9
    expected (P about 0.03 after the look-elsewhere effect). Bases 47 and 49
    would decide it. (chapter 17)
42. (Answered in chapter 23: chance; the cluster did not grow to -38, but negative bases have a general excess of empty bases, P = 0.03.) Six of the eight empty negative bases up to -35 are multiples of 3
    (P = 0.06 for those not named in advance). Chance? (chapter 14)
43. (Answered in chapter 23: yes, proven; integers are base -4 numbers in blocks of four digits.) In base `-n+i`, positive integers occupy lengths in runs of one parity.
    For `-1+i`, are the lengths exactly the residues 1 and 4 mod 8? (chapter 14)
44. (Partly answered in chapter 23: top digits explain a third to a half; the rest sits in a few bases and a 12% excess under `0^0 = 1`.) Per-base expected counts vary by about 20% beyond sampling error, and
    forced top digits explain part of it. What explains the rest? (section 11.2a)

## Round 3: questions raised by chapters 11 to 18

Each question has a longer statement, with its motivation and a first
attack, in [questions-round3.md](questions-round3.md).

45. (Answered in chapter 20: yes, up to slightly beyond `ln b / ln ln b` digits (Theorem 20.3); counting multisets cannot go further.) Count digit multisets instead of strings. Does this show that almost all
    bases have no solution with at most `(1 - eps) ln b / ln ln b` digits,
    twice the range of Theorem 11.2? (proof)
46. (Answered in chapter 20: Theorems 20.11 and 20.12 give the 3-adic and 5-adic laws; by Theorem 20.8 `T(p^e)` is everything for `p >= 7`.) Describe `T(q)`, the residues of `x^x - x` mod `q`, for `q = 3^e` and
    `5^e`, and prove `T(p^e)` is everything for `p >= 7`. (proof; Lemma 15.12)
47. (Answered in chapter 19: the new sieve is about 11x faster; 7- and 8-digit lists extended.) Add the prime powers 4, 8, 16, 9, 27, 81, 25, 125 to the `kdigit` sieve.
    (computation; Theorem 15.13)
48. (Answered in chapter 19: the right factor is the root count mod `p^e`; it does not explain the 5-digit excess.) Do 2-, 3- and 5-adic root densities in the root heuristic explain the
    5-digit excess, 6 found against 2.42 predicted? (computation; section 11.4)
49. (Answered in chapter 19: 4-digit counts are Poisson and fit; 5-digit solutions in bases 13 to 99 are an excess of about 9 times (recalibrated in chapter 22).) A defect spectrum for short solutions: the test of section 11.1 at 4 and
    5 digits, with a `kdigit` offset. (computation)
50. (Partly answered in chapter 25: true for bases up to `10^3301`; at most 30 in almost every base.) Does every base have at most two 3-digit solutions under `0^0 = 1`?
    (proof; Theorems 15.7 and section 18.2)
51. (Partly answered in chapter 20: `x^n + 25` solved for odd prime powers; `x^n + 3` reduced to a regulator condition.) Solve the families `(1,x,2)` and `(1,x,3)`, that is
    `b(b+x) = x^n + 3` and `x^n + 25`. (proof)
52. (Partly answered in chapter 20: `n` bounded in terms of `x` and the class order; none for `x <= 10^4`.) Settle the case `x == 0 (mod 8)` of `b(b+x) = x^n + 1`. (proof; 18.1.9)
53. (Answered in chapter 20 under GRH: `d | x` occurs, so only the Diophantine condition can close the loophole.) How large are the orders of mixed ideal classes in `Q(sqrt(x^2+4))`, the
    one loophole of Corollary 18.11? (computation)
54. Prove Assumption R, which would make Corollary 13.11 unconditional. (proof)
55. Is the general weighted problem still NP-hard when solutions must be
    long? (proof; section 13.1.6)
56. Does the length tail beyond `ln b` (Conjecture 10.3) hold in many
    perturbed worlds? (computation)
57. (Answered in chapter 19: the shortfall is not caused by the last digit.) Does the factorion shortfall survive offsets `j b (b-1)`, which also keep
    `n mod b`? (computation; question 41)
58. (Answered in chapter 19: the refined model fits forced-residue cells, 207 against 208.5; short lengths run 1.5x high.) Narcissistic numbers (weights `x^d`) as a model test: residue factors
    that change with the length, and doubling in odd bases. (twist)
59. (Answered in chapter 21: `N == digit sum (mod x)`; even `x` double; the model fits.) Munchausen numbers in the Pisot base `(x + sqrt(x^2+4)) / 2`. (twist)
60. (Answered in chapter 21: odd/odd bases double, as the model predicts.) Parity doubling in AFS rational bases. (twist; section 16.5)
61. (Answered in chapter 21: the problem is linear and finite; exact count for degree 2; a free factor `q` per factor of `B - 1`.) A function-field analogue in `F_q[T]` with weights `d^|d|`. (twist)
62. (Partly answered in chapter 21: only 1, 2, 4, 5 up to `34!`; the model fails; finiteness open.) Are there finitely many solutions in the factorial number system? (twist)
63. (Answered in chapter 21: no doubling, as predicted.) Eisenstein bases `-n + omega`: no parity doubling predicted. (twist)

## Round 4: questions raised by chapter 22

64. (Answered in chapter 25 for linear identities: two families; other mechanisms need an extra coincidence; Conjecture 25.8.) Is every short solution under `0^0 = 1` beyond some size a member of an
    algebraic family, such as the binomial families of Theorem 22.6? Do other
    identity families exist, for example with `p x^x` a `j`-th power for `p`
    not a `j`-th power, or with two large digits? (chapter 22)
65. (Partly answered in chapter 25: it is the next family member, and no other 3-digit solution exists up to `10^3301`.) Is `(1,6,46666)` in base `46666^23333 - 3` the next 3-digit solution under
    `0^0 = 1` after `(1,7,1)` in base 904? (chapter 22)
66. Apply the base-by-base calibration of section 22.4.1 to the 4-digit list
    and to the long solutions of bases 12 to 40, as a check on section 11.1.
67. Factorions: what could separate `D = 0` from every small offset that keeps
    all residues up to `b+1` and mod `b^3`? (chapter 23)
68. (Answered in chapter 26: with the corrected variance base 19 is at `z = -2.9`, one case of 42.) Why is base 19 low in its near-solutions under `0^0 = 0`, not only in its
    solutions? (section 23.5)
69. Prove the length runs of positive integers in base `-n+i` for `n >= 2`.
    (section 23.4)
70. (Partly answered in chapter 26: it survives the corrected variance at `z = 3.0`.) Why is the model about 12% low under `0^0 = 1` in every parity?
    (section 23.5)
71. Do the long integer solutions under `0^0 = 0` really have fewer zeros
    than the model, 29 against 42.5 in bases 12 to 41? (section 24.6)

## Round 5: directions and questions from the whole library

Seven broad directions and the full statements of these questions, with
their motivation and a first attack, are in
[questions-round5.md](questions-round5.md).

72. (Answered in chapter 26: 284 against 297 to 304; the worlds disagree, driven by odd-base factorions and Pisot bases.) A pooled test of `D = 0` against the near-solutions.
73. (Answered in chapter 26: the swap lemma; design effect 1.5 to 3.5; no verdict about `D = 0` changes.) Near-solutions at different offsets are not independent.
74. (Partly answered in chapter 26: a class mod `2x` in even `x`; the excess shrinks to P about 0.05.) Why the Pisot bases exceed their near-solutions.
75. (Answered in chapter 27: every order needs at least the top-down entropy, so 1.638^b holds for all orders (Theorem 27.2).) The entropy bound for other orders.
76. (Answered in chapter 27 in the oracle model: the exact tree is optimal up to a factor about linear in `b`, up to base 21.) Certificates of emptiness in an oracle model.
77. (Answered in chapter 27: CP-SAT and CaDiCaL grow 1.95 to 2.3 per base, worse than the engine.) A constraint solver as a search that is not a tree.
78. (Answered in chapter 27: unit sizes are explained by their type; deeper units balance shards; `--unit-stats`.) The law of subtree sizes.
79. (Answered in chapter 27: no; bottom digits make the tree 2.5 to 13 times larger in bases 16 and 32.) Bottom-up information in bases with a small radical.
80. Assumption R when `b - 1` is prime.
81. The length shares as a theorem in the model.
82. Is `k(B)` always the number of factors of `B - 1`?
83. A model that keeps the Frobenius blocks.
84. Open lengths in the factorial system.
85. (Answered in chapter 26: image share 0.21 to 0.14; forced top digits close two thirds of the gap.) The image and in-degrees of `F`.
86. (Answered in chapter 26, negatively: low-digit mixing does not track the model error.) A mixing statistic for every world.
87. Narcissistic numbers in even bases 15 to 20.
88. Chains with many self-paying digits under `0^0 = 1`.
89. A prefix test for the Gaussian base `-4+i`.
