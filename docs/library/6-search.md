# 6. The cost of finding all solutions

`docs/algorithm.md` describes the search and `docs/comparison.md` measures it.
This chapter explains where its cost comes from, why the ideas I tried do not
lower it, and what this means for base 100.

## 6.1 Growth rates

| set | size | growth per base |
|---|---|---:|
| digit multisets with at most `b` digits | `C(2b, b) ~ 4^b / sqrt(pi b)` | 4.0 |
| combinations the Python search checks | `nb7` in `src/nb.py` | 3.9 |
| nodes of the prefix-pruned tree | measured | 1.87 |

Base 38 takes 520 seconds on the test laptop, base 40 takes 36 minutes, and
each further base costs about 1.9x more.

## 6.2 Where the tree comes from

At the top of the tree the search fixes the counts of the largest digits. The
leading digits of the sum are then mostly small digits, and a small digit only
adds a lower bound on its own count. So the top levels prune almost nothing.
For base 21 and `d = 20`, each node at level `k = 19` has 15 children on
average.

Many of these children are atypical. They give a large digit far more copies
than a random number would have. Such a node survives until its free digit
positions run out. In base 21, the nodes at the widest level carry 12.5 large
digits on average, against 7.6 for a random number.

`analysis/typical.py` measures this effect. It drops every node with more than
`s` large digits above the random expectation. This is not a valid search; it
only measures the tree. The counts are for `d = b-1` under `0^0 = 1`:

| base | `s = 2` | `s = 4` | `s = 8` | full tree |
|---:|---:|---:|---:|---:|
| 16 | 2,260 | 3,669 | 4,536 | 4,557 |
| 19 | 8,927 | 17,335 | 27,621 | 28,422 |
| 21 | 15,262 | 36,241 | 75,936 | 82,468 |
| 23 | 61,981 | 160,748 | 330,597 | 366,889 |

From base 16 to 23, the full tree grows 1.87x per base, and the tree with
`s = 2` grows 1.60x per base. At base 23 the atypical nodes make up 83% of the
tree. An exact search must keep them, because a node with many large digits can
still lead to a solution. In a random 100-digit number, the count of digits in
the upper half has a standard deviation of 5. So a cap on `s` would miss real
solutions.

## 6.3 Ideas that do not lower the growth rate

- Meet in the middle on digit values. Split the digits into large and small
  values. The small values only change the low part of the sum, but that part
  is `A + L`, where `A` depends on the large counts and `L` on the small ones.
  The digit counts of a sum do not split into a function of `A` plus a
  function of `L`. So there is no key on which to join the two halves.
- An exact join exists if the bottom `q` digits are enumerated as a string.
  Then `B - F_small(B)` must equal a value computed from the large counts
  alone. But `q` must cover the weights of the small digits, which is about
  half the number. That needs about `b^(b/2)` strings, far more than `1.87^b`
  nodes.
- Meet in the middle on positions. Splitting `n` into a top string `T` and a
  bottom string `B` gives the exact equation `T * b^q - F(T) = F(B) - B`. Each
  side then has `b^(d/2)` strings, which gives up the symmetry that makes
  multisets cheap.
- Lattice reduction. The equation `sum (w(s_i) - s_i b^i) = 0` is a subset-sum
  problem with density about `b / log2(b)`, which is above 1. At that density
  lattice methods fail, because the relaxed problem has many solutions.
- Congruences. `n` is linear in the counts modulo `b^j`, and
  `n == digit sum (mod b-1)`. Both constraints involve every count, so they
  only prune near the leaves, where the tree is already small.
- A feasibility check on the interval removes 10 to 13% of the nodes. That is a
  constant factor.

## 6.4 Why I do not expect a fast exact search

The random model of chapter 5 describes a solution as a coincidence: one digit
multiset among about `4^b` that happens to reproduce itself. An exact search
must give every plausible multiset a reason why it fails. Chapters 2 and 3 show
that the only structure available is local. It consists of identities between
single powers, such as self-paying digits, and the leading digits that an
interval of sums fixes. The prefix-pruned tree already uses the leading digits. The congruences
of section 1.6 cut the count by a constant factor at most.

Consider a search with polynomial cost, or with a growth rate near 1.3x per
base. It would need a way to rule out large groups of multisets at once,
without looking at them. None of the ideas in section 6.3 does that, and the data shows no
structure that would allow it. This is an argument, not a proof. A proof of a
lower bound would be a result in complexity theory, far beyond this question.

## 6.5 Short solutions are cheap

For a fixed length `k` the picture is different. Proposition 1.3 turns the
search around: enumerate digit strings and solve for the base. By
Proposition 4.1, the cost per base is a power of `log b`. Every solution with
at most 6 digits, in every base up to `10^4.6`, took 10 minutes in Python
(chapter 3). For 3 digits the search covers every base up to `10^51.5`.

## 6.6 Base 100

The `fast` engine handles bases up to 127, for numbers with at most 62
digits. Exhaustive results for base 100, both conventions:

| digits searched | nodes | time |
|---:|---:|---:|
| up to 30 | 141,449 | 0.055 s |
| up to 40 | 15,778,515 | 0.88 s |
| up to 45 | 531,426,476 | 21 s |
| up to 50 | 3,611,595,932 | 139 s |

No base-100 number with 50 digits or fewer is a nontrivial Munchausen number.
The model expects about 0.002 such solutions. A run up to 55 digits finished
98% of its work units in 100 minutes without a solution, and was stopped
before the end.

The expected solutions have 97 to 100 digits. At 1.9x per base from base 40,
base 100 needs about `10^20` seconds. Even a growth rate of 1.6x per base would
leave about `10^15` seconds.
