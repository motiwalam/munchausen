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

19. (Answered in chapter 17: forced residues multiply the count by 19.9 under `0^0 = 0` against 16.9 predicted.) A sharp test of the model: force `w'(x) == x (mod b-1)` in perturbed
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
54. (Partly answered in chapter 29: R as stated is false for short strings; it reduces to one exponential sum `rho(b)` per base, and Corollary 13.11 holds unconditionally for `12 <= b <= 6000`. Answered in its qualitative form in chapter 30: the refined Poisson law holds in the limit for every base without R (Theorem 30.5); the rate `O(1/b)` is open.) Prove Assumption R, which would make Corollary 13.11 unconditional. (proof)
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

64. (Answered in chapter 25 for linear identities: two families; other mechanisms need an extra coincidence; Conjecture 25.8. Partly answered in chapter 32 for 3 digits: with an even large digit behind a non-square leading digit only finitely many, none with the other digits at most 20 (Theorems 32.2, 32.3); open where the field `Q(sqrt n)` changes with `x`. Chapter 36: in the last position an odd large digit gives only finitely many for each pair of small digits (Corollary 36.10); open in the middle and leading positions.) Is every short solution under `0^0 = 1` beyond some size a member of an
    algebraic family, such as the binomial families of Theorem 22.6? Do other
    identity families exist, for example with `p x^x` a `j`-th power for `p`
    not a `j`-th power, or with two large digits? (chapter 22)
65. (Partly answered in chapter 25: it is the next family member, and no other 3-digit solution exists up to `10^3301`. Chapter 32 adds every base for an even, non-leading large digit with the other digits at most 20 (Corollary 32.4).) Is `(1,6,46666)` in base `46666^23333 - 3` the next 3-digit solution under
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
78. (Answered in chapter 27: unit sizes are explained by their type; deeper units balance shards; `--unit-stats`. Chapter 31 adds `--shard-by size`.) The law of subtree sizes.
79. (Answered in chapter 27: no; bottom digits make the tree 2.5 to 13 times larger in bases 16 and 32. Chapter 31: a last-digit check on nodes with one free slot prunes 17% but costs 2% more cycles.) Bottom-up information in bases with a small radical.
80. (Partly answered in chapter 29: R reduced to `rho(b)` (Theorem 29.15), proven by computation up to base 6000; square-root cancellation seen for `b - 1` prime; no `o(p)` bound in the literature. Chapter 30: R follows from `O(p)` collisions of `x^x - x` modulo `p` (Corollary 30.8); computed about `2 (p - 1)` for `p < 10^5`.) Assumption R when `b - 1` is prime.
81. (Answered in chapter 29: proven with error `O(1/b)` (Theorem 29.1); the sum over lengths tends to 1.) The length shares as a theorem in the model.
82. (Partly answered in chapter 29: yes when a factor has degree prime to `e - 1`, for non-squarefree `B - 1`, and for `e <= 10`; always at most one more; open from `e = 11`.) Is `k(B)` always the number of factors of `B - 1`?
83. (Answered in chapter 29: the block model fits 16 of 21 factor types within 17% and cuts the per-orbit misfit by 4; repeated factors still miss.) A model that keeps the Frobenius blocks.
84. (Answered in chapter 29: a top-digit model closes about half the lengths; open below `34!` are 8, 10, 13, 14, 15, 18, 19, 20, 24, 26, 28, 29, 30, 32; the census extension to `L = 40` was not run.) Open lengths in the factorial system.
85. (Answered in chapter 26: image share 0.21 to 0.14; forced top digits close two thirds of the gap.) The image and in-degrees of `F`.
86. (Answered in chapter 26, negatively: low-digit mixing does not track the model error.) A mixing statistic for every world.
87. Narcissistic numbers in even bases 15 to 20.
88. Chains with many self-paying digits under `0^0 = 1`.
89. A prefix test for the Gaussian base `-4+i`.

## Round 6: directions and questions from the whole library

Seven directions, the full statements of these questions with their
motivation, a first attack and leads, four proposed workloads and a list of
problems found in the library are in
[questions-round6.md](questions-round6.md).

90. (Answered in chapter 34: the count over lengths 2 to `b` is the trace without the first entry (Proposition 34.5); the rows converge (Theorem 34.6); `tr = 1 + C/b` with `C = 1.104636`, one eigenvalue (Proposition 34.8, Heuristic 34.9); the refined count is a sum over characters (Proposition 34.10), with `e^-2` for the order-2 character under `0^0 = 1` (Theorem 34.12); the lead's `3/b` is the length-1 entry.) The expected count is the trace of a stochastic matrix.
91. (Answered in chapter 35: for `q` prime to `b (b - 1)` the error is at most `(q - 1) e^(1/8) exp(-(1 - gamma)^2 (k - 1)/64)`, independent of `ord_q(b)` (Theorem 35.1, Corollary 35.2); the measured crossover is 10 digits for `q` = 3, 5, 7 and 12 for `q = 9`; the arrangement factors have mean 1 and do not explain the short-solution excess (section 35.1.4); the moduli 4 and 8 never qualify.) Arrangements and the local factor.
92. (Answered in chapter 35: the two heuristics agree on totals at lengths 6 to 12; per base only the refined model with the top digit forced matches the window calibration, because the root heuristic averages the parity factor; no missing factor (section 35.2).) The two heuristics at medium lengths.
93. (Answered in chapter 34: zero-free near-solutions in odd bases (1.26) and one zero under `0^0 = 1` in even bases (1.30); perturbed worlds show no gap between the conventions; with the between-world scatter the excess is about 2 standard deviations and not a third kind of correction (Heuristic 34.4).) Where the 12% excess under `0^0 = 1` sits.
94. (Answered in chapter 34, negatively: no deficit in even bases; in odd bases the deficit is the zero-free surplus of question 93; the forced top digits do not lower the expected zeros (section 34.2).) Do near-solutions share the zero deficit of question 71?
95. (Advanced in chapter 35: the identity modulus is `b - 1`, and odd bases get the factor 2 with no convention (Propositions 35.5 and 35.7); the census is open.) Bijective numeration: no zero, and a self-paying digit in every base.
96. (Answered in chapter 33: a sufficient condition for every weight (Theorem 33.12); under abc exact for solutions with one dominant digit (Corollary 33.15); `x!` never meets it (Proposition 33.13).) A criterion for identity families.
97. (Answered in chapter 33: finite for a large last or middle digit, with explicit bounds (Theorems 33.4, 33.5); a leading digit reduces to `4x x! + s^2 = U^2`; complete for the other digits up to 10 except that case (Theorem 33.6); two large digits reduce to Brocard type under GRH (Proposition 33.8).) Three-digit factorions are finite, except for a Brocard case.
98. (Answered in chapter 33: no for `k = 2`, infinitely many (Proposition 33.9); under GRH a large last digit leaves only `x` with `G_x` intersective, rational roots for `k <= 5` (Theorem 33.10); GRH alone does not give finiteness for `k >= 4`; abc does for each prefix (Theorem 33.19).) Factorions of every length under GRH.
99. (Partly answered in chapter 33: none found up to `t = 10^5`; one-step chains give only base 64 (Proposition 33.22); the length is `c + O(log b)` (Proposition 33.21); longer chains need a coincidence (Heuristic 33.23).) Long structured solutions under `0^0 = 1` (speculative).
100. (Answered in chapter 35: every base `b >= 27` has `0 < |n - F(n)| < b^(b-1-T)` with `T = sqrt(b / e) - O(1)` explicit (Theorem 35.13); `t >= 2` for every `b >= 77` (Corollary 35.14).) Near-solutions that provably exist (speculative).
101. (Answered in chapter 35, negatively for this route: the averaged bound is at least `e^(-2A - o(1))` times that of Proposition 20.2 (Proposition 35.9, Corollary 35.10); averaging excludes solutions of length up to `(ln b)^C` with few digits of weight at least `sqrt(b)` (Theorem 35.12).) Beyond `ln b / ln ln b` by averaging over bases.
102. (Partly answered in chapter 32: abc bounds `x` for one large digit in every position and parity (section 32.1.6); unconditional for an even large digit behind a non-square leading digit (Theorem 32.2) and for a fixed square class (Proposition 32.6); two large digits open. Answered in chapter 33 for one large digit: under abc `x <= (2 + O(eps)) B + C_eps` when `R != 0` (Theorem 33.16), every length in Theorem 33.19; with `c < rad^(7/4)` the list is complete for two digits up to 200 (Corollary 33.18); two large digits `u >= v` remain only for `v` above about `u/2` (Proposition 33.20).) The abc conjecture and the 3-digit list.
103. (Answered in chapter 34: 241 rows, 56 groups; far from uniform as a whole (Fisher P `2 * 10^-9`) because of selection; the 12 groups named in advance look uniform (Fisher P = 0.74); no lean toward deficits (Heuristic 34.14).) A ledger of P values.
104. A pre-registered census of bases 42 to 46.
105. The first `b`-digit solution under `0^0 = 1`.
106. (Answered in chapter 34: no correlation of neighbouring residuals once the top digits are forced; no shared near-solution multisets; uncorrelated top digits; but the two conventions in one base correlate at +0.78 (section 34.5, Heuristic 34.15).) Are neighbouring bases independent?
107. (Narrowed in chapter 35: the class is not an invariant of the multiset; the gcd within multiset groups is `2x` only at length 4 (section 35.3.3).) The class modulo `2x` in even Pisot bases.
108. (Answered in chapter 35: the ideal of `(x - y)(beta_i - beta_j)` over the exchanges, `(beta - 1)` for geometric place values, with rational integers `|f(1)| Z` and the residue factor an index (Propositions 35.5 to 35.7); checked in 67 systems; the question's "exactly when" needs the digit differences and connectivity.) One invariant-residue proposition for every positional system.
109. Is anything about the middle digits cheap? (speculative)
110. A last-digit factor in negative bases?

## Round 7: questions raised by chapter 29

111. In `F_q[T]`, can a squarefree `B - 1` whose factors all share a divisor
     with `e - 1`, with no factor of degree 2 and `q >= e - 1`, have
     `k(B) = omega(B - 1) + 1`? Does condition (b) of Theorem 29.11 (2) for
     `k = 2, 3` already rule it out? First test: `e = 11`, factors of
     degrees 5 and 6, `q = 11, 13`. (proof; section 29.2.5)
112. Is `max over h != 0 of |sum over x <= p of e(h (x^x - x)/p)|` of size
     `O(sqrt(p log p))` (Conjecture 29.18)? A weaker target suffices for
     Corollary 13.11: the sum is below `p - 3 ln p` for every `h` and every
     initial segment of length at least `p/2`. Can the subgroup sums of
     Cilleruelo and Garaev give it? (proof; section 29.3.5)
113. (Bypassed in chapter 30 for the Poisson limit: anti-concentration works for any modulus, at the rate `exp(-c ln b / ln ln b)` (Theorem 30.5).) Prove `rho(b) < 1 - c` for composite `b - 1` whose prime factors are all
     below `b^(1/2)`. Proposition 29.19 handles one prime at a time.
     (proof; section 29.3.4)
114. (Partly answered in chapter 34: `sum over j of c_j = C = e/(e-1)^2 + 1/(2e)` plus a series of size `2.2 * 10^-5` (Proposition 34.8); the refined model's term is open.) What is the first-order term `c_j / b` of Proposition 29.7 in the
     refined model, and does `sum over j of c_j` (1.1046) have a closed
     form? (proof; section 29.1.4)
115. The block model misses the types of `B - 1` with a repeated factor
     (ratio 2.09 for two double roots in `(5, 4)`) and predicts 5 to 6
     solutions where there are none. Is there an exact obstruction on the
     nilradical, like Theorem 29.11 (3)? (proof; section 29.4.3)
116. Factorial system: why is `L = 13` open with the largest model mean
     (0.80) but only 3 to 6 offsets with near-solutions? Keep the top digits
     over the positions of the two largest values. (computation; section
     29.5.2)
117. Factorial system: reduce the variance of the top-digit model beyond
     `L = 50`, for example by importance sampling on the largest digit and
     its count. (computation; section 29.5.3)

## Round 8: questions raised by chapter 30

118. Prove `#{x, y <= p - 1 : x^x - x == y^y - y (mod p)} <= p^(2 - delta)`
     for some `delta > 0`. By Corollary 30.8 this gives Assumption R with a
     power rate for prime `b - 1`. The method of Cilleruelo and Garaev
     handles `x^x`; the shift needs a new idea for the fibres
     `x^x == x + c`, `c != 0`. (proof; Conjecture 30.9)
119. An inverse Littlewood-Offord theorem for random choices. If a sum of
     `k` independent steps, each uniform on a fixed multiset of `M`
     residues modulo `q`, hits one class with probability above `K/q`, must
     most of the multiset lie in a short progression? Then Assumption R
     would follow from a statement about `x^x - x` alone. (proof; section
     30.1.6)
120. Can the dissociation argument of Theorem 30.5 also use the digits near
     `b`, whose weights are known modulo a prime `b - 1 = p`
     (`(p - t)^(p-t) == (-t)^(1-t)`), and push `rho*(b)` below a power of
     `b`? (proof; section 30.1.4)
121. What is the asymptotic of `(1/Y) sum over a <= Y of f(a)`, the density
     of fixed points of `x -> x^x mod a` averaged over `a`? The data suggest
     `Y^(-0.44)` for `Y <= 300`. (proof; section 30.2.4)
122. Three-digit narcissistic numbers: is there an exact count, or an
     average order, for `s2 b^2 + s1 b + s0 = s2^3 + s1^3 + s0^3`? The model
     says a bounded mean; the cubic surface suggests local factors again.
     (proof; section 30.3.4)
123. Write the coupled model of section 13.2 for factorions (weights `x!`)
     and check that Theorem 30.3 gives its Poisson limit, as section 30.1.5
     claims. (proof; section 30.1.5)

## Round 9: questions raised by chapter 31

124. (Answered in chapter 37: with the residue, the interval fails 0.0% to
     7% of these nodes, too few to pay for a sorted table; the last digit
     of the pair fails 10% to 28% of them, and the last two digits pay,
     section 37.2.) Is there a cheap exact test for nodes with two free slots? The
     congruence alone reaches almost every class. The pair `(y_1, y_2)`
     must also put `S = t + w(y_1) + w(y_2)` in the interval of the prefix,
     a 2-sum problem over `k` values. How often does no pair satisfy both,
     and can a sorted table per level answer it in a few instructions?
     (computation; section 31.4.2)
125. (Answered in chapter 37: the extra instructions are register and
     stack moves of the two byte residues; they run in idle issue slots
     and cost no cycles, section 37.3.) Where do the extra cycles of the
     residue rule go? Two residues per node
     cost 6% to 13% more instructions, but computing a child's residue
     only after its forced digits saves no cycles. A profile of the loop
     over `e` with and without the rule would say whether the larger node,
     the extra branch or the test before the interval costs the time.
     (computation; section 31.2.4)
126. A better size predictor for `--shard-by size`. Does the node count of
     each unit after one or two more levels, times the type fit, cut the
     within-type error of 0.5 in `ln(nodes)`? What is the best balance for
     64 and 256 shards at depth 4, and what does the probe cost?
     (computation; section 31.5)
127. Each free slot multiplies the subtree by about 1.8, and 43% of the
     nodes have one free slot (Table 31.1.1). Is the law of the free slots
     over the exact tree a fixed geometric law, as the branching process of
     section 27.5 suggests? Then the share of the nodes that a test on `f`
     free slots can reach is known in advance for every base.
     (computation; section 31.1.2)
128. (Answered in chapter 37: the mask costs one `or` per child and one
     compare per new prefix digit; three last digits save 3% to 8% of the
     cycles, and they are on by default, section 37.1.) Do the last digits
     pay in another form? A check of the last digit
     removes 17% of the nodes at base 26 but costs 2% more cycles. A table
     of `w(y) mod b` per residue class, and a bit mask of the digits that
     the unknown positions still hold, would make it a few instructions. Is
     the mask cheap to keep up to date as the prefix grows? (computation;
     section 31.4.2)

## Round 10: questions raised by chapter 32

129. (Answered in chapter 36 for the last position: there the field of
     `R` is imaginary once `x > W + q^2/(4p)`, and Theorem 36.9 bounds `x`
     uniformly in `q`. The middle position with `x` odd and the leading
     position remain open.) Uniformity over fields. Is there a bound for the solutions of
     `U^2 - n V^2 = R`, with `V` a power like `x^(x/2)`, that is uniform
     over the fields `Q(sqrt(p x))` with `x` odd? This would close the
     3-digit problem with one large digit up to computation. Lead: results
     on `y^2 = a x^n + c` that are uniform in `n`. (proof; section 32.1.6)
130. (Answered in chapter 36 for the last position: every square class at
     once, Corollary 36.10. The middle position remains.) Other square classes. Proposition 32.6 gives finiteness for odd `x` in
     any fixed square class `x = lam t^2`, and Proposition 32.7 closes
     `lam = 1` for `p, q <= 20`. For `lam > 1` the linear form has five
     logarithms and the bound on `t` is about `10^10`. Is there a better
     route, for example an `l`-adic bound at a prime `l` dividing `lam`?
     (proof and computation; section 32.1.6)
131. Four digits with a binomial prefix. Carry out section 32.1.7 for
     `(p, q, r, x)` with `q^2 = 3 p r`, `x` even and `3 | x`: a Thue
     equation in `Q(p^(1/3))` with a 2-adic bound. (proof; section 32.1.7)
132. (Answered in chapter 31: the engine already iterates to the fixed
     point, which saves 1.46 to 1.47 times the nodes in bases 20 to 33, a
     constant factor (section 31.3.2).) A fixed-point bound for the exact
     tree: how many nodes does the iterated interval remove? (computation;
     section 32.3)

## Round 11: questions raised by chapter 33

133. The leading Brocard case. Is `4x x! + s^2 = U^2` with
     `s^2 = q^2 + 4Ax` solvable for any `x > 10`? Push the sieve of section
     33.1.4 to `x = 10^9`, as Berndt and Galway did for Brocard. This would
     also reach the Laishram-Shorey bound for digits up to about `10^6`.
     (computation; section 33.1.5)
134. Sharper unconditional bounds. For `|K|` linear in `x` the bound
     `Delta^0.45` is far from the truth: the least inert prime up to
     `4 * 10^6` is at most 79. An explicit Burgess bound for imaginary
     quadratic characters would cut `X0(B)` of the last position from a
     power of `B!` to about `(B!)^(1/4)`. (proof; section 33.1.3)
135. Two large digits in the factorion world. Run the GRH reduction of
     Proposition 33.8 as a computation for `u, v <= 10^4`. How many pairs
     have `K_A` or `K_B` a square, and do any survive a sieve?
     (computation; section 33.1.6)
136. The comparable range for `x^x`. Proposition 33.20 leaves
     `u/2 <~ v <= u`. Is there a conditional statement that covers it, such
     as a 4-term abc with a better exponent for this shape, or Vojta's
     conjecture for the surface `U^2 = 4l (u^u + v^v) + R`? (proof; section
     33.4.4)
137. Intersective polynomials for `k >= 6`. Are there prefixes `t` for which
     `G_x` is intersective without a rational root for infinitely many `x`?
     (proof; section 33.2.2)
138. Theorem 15.14 with cycles. Proposition 33.22 used only self-paying
     digits. Do swaps (2-cycles of `phi`) allow a family with a one-step
     chain? (proof and computation; section 33.5)

## Round 12: questions raised by chapter 34

139. Between-world variance. In perturbed worlds the ratio `lambda / model`
     of one parity and convention ranges from 0.84 to 1.16 across seeds,
     even with the top digits forced. That is 1.3 to 1.5 times the
     clustered sampling error. What carries this variance? Candidates are
     the short lengths of small bases (base 13 alone moves the odd
     zero-free cell by 0.1), the fourth and later top digits, and the low
     digits of `F` modulo `b`. The answer fixes the error bar of every
     world-level ratio in the library. (computation; section 34.1.5)
140. The zero-free surplus in odd bases. Zero-free near-solutions in odd
     bases 12 to 26 are 1.26 times the model (1.17 without base 13). Does
     the surplus hold in odd bases 27 to 41, with a rerun of
     `r5e_int_offsets.py` that keeps the strings? Is it a local factor of
     short lengths, as section 11.4 has for short solutions? (computation;
     section 34.1.3)
141. Uniform first-order trace. Prove `tr M_b - E_1 = 1 + C/b + o(1/b)` by
     bounding `|E_(b-j) - s_j - c_j/b|` uniformly for `j <= C' ln b`. With
     Theorem 29.5 this would finish Proposition 34.8. (proof; section
     34.3.3)
142. The other characters. Which property of `b - 1` makes
     `sum over t not in {0, q/2} of tau_t(b)` large (0.36 at `b = 13`, 0.19
     at 25, 0.06 at 64)? Is it bounded by a function of the largest powers
     of 2 and 3 that divide `b - 1`? (proof and computation; section
     34.3.4)
143. A pre-registered ledger. Before the runs of question 104, write down
     the model's prediction and a two-sided test for every group of Table
     34.4.2.1 that extends to fresh bases. Add the results to the set named
     in advance. (computation; section 34.4)

## Round 13: questions raised by chapter 35

144. Linear `t`. Can near-solutions with `t >= c b` be proved in every
     base? The obstacle in Theorem 35.13 is the zone of values that the
     matched digits must avoid. A fixed-point version that lets matched
     digits be large and feeds their weights back into the steering might
     remove it. The construction, run exactly, already reaches 0.13 `b` to
     0.5 `b`. (proof; section 35.5)
145. The identity factor at short lengths, in closed form. Table 35.1.4.1
     computes `(b - 1) P(b - 1 | G(c))` by the exact walk. Is there a
     formula in the small primes of `b - 1` and the length, as in
     Proposition 35.7 but for the digits up to `X_k(b)`, that gives the
     short-solution rates of all worlds (Munchausen, factorions,
     narcissistic) at once? (proof and computation; section 35.1.4)
146. Equidistribution on average over windows. Prove, for some
     `theta > 0`, that sums of `K` weights `x^x` with `z < x <= X` hit
     `0 (mod b - 1)` for at most a share `B^(-theta)` of the pairs
     (multiset, window base). By Proposition 35.8 this would extend
     Theorem 20.3 to `alpha = 1 + theta`. (proof; section 35.4)
147. Sharper arrangement bounds. Replace `gamma` in Theorem 35.1 by a
     quantity that uses the varying units `b^(2j)(1 - b)`, so that strings
     with small digits and large `q` are covered, and compare with the
     measured `e^(-0.35 k)`. (proof and computation; section 35.1)
148. Theorem 35.12 with the congruence. Combine the window count of
     Theorem 35.12 with the condition `b - 1 | G(c)` for solutions whose
     small part is long and dissociated. Does it give a range beyond
     `(ln b)^C` for strings with few large digits? (proof; section 35.4.3)

## Round 14: questions raised by chapter 36

149. A computable bound for the last position. Theorem 36.9 bounds an odd
     last digit `x` by about `10^40`. Mignotte's bounds for three
     logarithms, or a primitive divisor theorem for twisted sequences
     `tau gamma^n - tau' gamma'^n` that is uniform in the height of `tau`,
     would bring the bound within reach of the sieve and close the last
     position for `p, q <= 10`. (proof and computation; section 36.3)
150. A class-group sieve. For `x` with `J` not ambiguous, a solution needs
     `[J] = [A]^(-x)` for one of the `2^omega(x)` ideals `A` of norm `x`,
     an event of chance about `2^omega(x) / e`. Can this be tested fast
     enough, with forms of discriminant `-4D`, to run beyond `10^10`?
     (computation; section 36.3)
151. (Partially answered in chapter 38: for the 25 families with `pA` a
     square, odd prime powers `x` are effectively bounded without linear
     forms in logarithms (Theorem 38.2); `(1, x, 1)`, `(1, x, 0)`,
     `(3, x, 1)`, `(3, x, 0)` and, up to `5^a > 10^9`, `(1, x, 3)` are
     closed for prime powers (Corollary 38.3). Open for `pA` not a square.)
     The middle position. Proposition 36.11 leaves the 25 families with
     `pA` a square for every `x`, and a density-0 set of `x` for the
     others. Is there a finiteness theorem for `x` prime, where `A` is a
     prime ideal and the class group has order about `x / log x`
     (`A = 1`) or the regulator is about `x` (`A > 1`)? (proof; section
     36.4.1)
152. (Answered in chapter 38: `(x, q, r)` with `x` even is a solution for
     only finitely many `x`, effectively, for every `q, r` (Theorem 38.6).)
     The leading position. Is there finiteness for the even `x` for which
     `Q(sqrt R)` has class number above `x^(1/6 + eps)`? These form a thin
     set, but it would be the first result in that case beyond fixed
     square classes. (proof; section 36.4.3)
153. Other weights. For factorions the last position gives
     `U^2 + |K| = 4p x!`, also imaginary, but `x!` is not a power. Which
     weights `w(x)` are perfect `x`-th powers up to a bounded factor on a
     large set, so that the argument of chapter 36 applies? (proof;
     section 36.6)

## Round 15: questions raised by chapter 37

154. The first unknown digit of a pair. It fails 24% to 47% of the nodes
     with two free slots (Table 37.2.1), more than the last digit, but
     needs the carry of `t + w(y1) + w(y2)` into lane `pp - 1`. Can a test
     on the top lanes of `t` and a table of `w(y) / b^(pp-1)` per level
     decide it for most pairs, and the rest by a full sum? (computation;
     section 37.2.2)
155. The GPU. With the tests, the CPU visits 0.53 to 0.57 of the nodes of
     the GPU. Does a port of the mask and the tables to
     `shaders/search.comp` pay on the subgroup engine, where the residue
     rule gave 1.18x? (computation; section 37.4)
156. Copies. The last-digit tests ignore the multiplicity of a digit in the
     last lanes. A second mask of the digits with two copies left would
     make them exact for two and three digits. How many more nodes would
     that remove, and at what cost? (computation; section 37.1.2)
157. Three free slots. The sums of three weights reach most classes and
     most last digits, so the mask would be dense. Does the last digit of
     a triple still remove a useful share of those nodes, 14% of the tree
     (Table 31.1.1)? (computation; section 37.2.3)
158. (Answered in chapter 37: `lowOk_of_isCompletion` and
     `pairOk_of_isCompletion` in `lean/Munchausen/Search/`, with
     `found_eq_solutions` for the search with both tests, section 37.5.)
     Lean. Lemma 37.1 and Propositions 37.2 and 37.4 are statements about
     multisets and digits. Can the verified search of
     `lean/Munchausen/Search/` run both tests, with a soundness lemma for
     each? (proof; section 37.5)

## Round 16: questions raised by chapter 38

159. Mixed solutions in the square families. For `x` with two prime
     factors, a solution of a middle family with `pA = k^2` needs the class
     of `Q = P_T / P_T'` to absorb `z^x`. Is there a version of Corollary
     18.11 for `k > 1`, where `Q(sqrt(x^2 + 4k^2))` has no small unit?
     (proof; section 38.2.4)
160. The biquadratic field. For `pA` not a square and `x` prime, is the
     class of `I^2` in `M = Q(sqrt(x^2 + 4pA), sqrt(pA))` ever principal
     with a generator of height `O(log x)`? A positive answer on a set of
     primes of positive density would close the middle position there by
     the trace argument. (proof; section 38.3.1)
161. A computable bound for the leading families with `|S| > 0`. Theorem
     38.6 gives `10^39` and more. With three logarithms and the `l`-adic
     places of `S`, can the bound for `(x, 1, 2)` or `(x, 2, 1)` be brought
     below `10^13`, within reach of the sieve? (proof and computation;
     section 38.4.2)
162. Prime powers `x = 5^a`, `a` odd, in `(1, x, 3)`. The Pell form in
     `Q(sqrt 5)` with `V` a power of 5 gives a bound by Proposition 32.6.
     Compute it and close `(1, x, 3)` for prime powers. (computation;
     Corollary 38.3)
163. Uniformity for the leading position. Theorem 38.6 depends on `A`
     through `sqrt(A)` and the primes of `Aq`, so with `q, r <= B` it gives
     about `x <= B^(B + o(B))`. Is there a bound polynomial in `B`, as
     Theorem 32.5 gives for an even `x` behind a non-square digit? (proof;
     section 38.4.2)

## Round 17: directions and questions from the whole library

A preface on where the project stands, its blind spots and the assumptions
nobody questioned, the full statements of these questions with their
motivation, a first attack, leads and an estimate of difficulty and payoff,
four proposed workloads and a list of problems found in the library are in
[questions-round7.md](questions-round7.md).

164. Which families of strings can be decided at all? A reduction through
     Theorem 25.7 (ii) seems to make templates with polynomial digits
     undecidable; are free-digit families decidable? (proof, logic)
165. Local and global obstructions for one free digit. Which middle
     families have a covering, and which are locally soluble everywhere?
     Lead: 10 of the 440 fail by parity, the other 430 pass six prime
     powers together. (proof and computation; section 32.1.3)
166. Which conjecture closes the middle position? The Lang-Waldschmidt
     conjecture with GRH, or LW alone? (proof, conditional; section 38.3.2)
167. Why no reduction step applies: every linear form of chapters 32, 36
     and 38 has an algebraic number that moves with `x`. Is a uniform
     reduction possible? (speculative)
168. Is three digits the limit of the S-unit method? The size of the
     discriminant for every number of digits and position. (proof)
169. The next 3-digit solution, unconditionally: the sieve of Theorem 25.11
     over all `10^14` strings with digits up to 46,700. (computation)
170. How many bases provably have a solution? Under `0^0 = 1` about
     `(ln X)^2` bases up to `X`, under `0^0 = 0` at least `sqrt(X)/2`.
     (proof)
171. A census by the number of distinct digit values, in all bases up to
     a bound. (search engineering)
172. Is the multiset map lumpable? Exhaustive `phi_b` for bases 8 to 14.
     (computation, Markov chains)
173. Testing the model at large bases through the top levels of the exact
     tree. (computation)
174. Selection and classification in the short-solution residual: base 10
     and the block `(3,3,6,6)`. (computation; section 35.1.4)
175. Search lower bounds in other models: fooling sets for every `b`,
     residue oracles, resolution and cutting planes. (proof, complexity)
176. Atypical nodes: can information outside the interval certify them?
     (search engineering; section 6.2)
177. A fully formal finiteness theorem for an exponential family: Theorem
     38.2 for `(1, x, 1)` and `(1, x, 3)` in Lean. (formalization)
178. The trust chain of the census and the sieves. (formalization and
     engineering)
179. An audit of the cited constants and a literature search. (referee
     work)
