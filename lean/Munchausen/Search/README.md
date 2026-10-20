# The verified exact search

These files hold a functional version of the exact search in
`fast/src/search.rs`, and a proof that it finds every solution and nothing
else. The Lean code favors reading over speed. It runs on small bases.

What is verified is the algorithm, in this separate Lean implementation.
The Rust engine is not verified. The tables below map each Lean function to
its Rust counterpart by hand, and `Examples.lean` checks by test, not by
proof, that both give the same solutions and node counts in bases 2 to 12.

## Files

| file | content |
|---|---|
| `Spec.lean` | digits of a `d`-digit number, the count form of `F`, the length bound, the specification `solutions b m` |
| `Dfs.lean` | an abstract depth-first search with pruning, and its soundness, completeness and no-duplicates lemmas |
| `Algorithm.lean` | the search itself |
| `Correctness.lean` | one lemma per pruning rule, and the main theorems |
| `Properties.lean` | `settle` reaches its fixed point, and the search has no duplicates |
| `Examples.lean` | runs against `output/b2-41-0.txt` and `output/b2-41-1.txt`, node counts against `fast search`, and kernel-checked solution lists |

## How the Lean code maps to the Rust code

| Lean (`Algorithm.lean`) | Rust (`fast/src/search.rs`) |
|---|---|
| `Params` (`b`, `d`, `ms`, `low`, `pair`) | `Params::new`, `prune.residue` for the conventions, and `prune.low`, `prune.pair` (`--low-digits`, `--low-pairs`) |
| `Node` (`cnt`, `pl`) | `Node`, the histogram `cnt`, and the known lanes of `lo` |
| `t`, `hi`, `rf`, `residue` | the fields `t`, `hi`, `rf`, `res` of `Node` |
| `clo`, `chi` | `Params::clip_lo`, and the clipping in `next_child` |
| `prefixLen` | the `eq_mask` and `leading_zeros` at the top of `settle` |
| `childAt` | `ck = occk + e` in `next_child` |
| `childCands` | the loop over `e` in `next_child`, with its `break` on `lo >= b^d` |
| `tryChild` | the body of that loop |
| `settle` | `Search::settle` |
| `firstDigitOk` | `first_digit_ok` |
| `resOk` | `Params::res_ok` |
| `sumW` | `t` plus the zero term `zlow1` in `low_ok` and `pair_ok` |
| `avail` | the mask `avail` of `Node`, and `Params::node_avail` |
| `lowDigitsOk` | the digit checks of `low_ok` and `pair_ok` (the shifted masks and the loops over `lcand`, `pcand`) |
| `lowOk` | `Params::low_ok` |
| `pairOk` | `Params::pair_ok` |
| `oneSlotFails` | `res_ok(k, res) && (L & 3 == 0 \|\| low_ok(..))` at its two call sites in `next_child` |
| `pairFails` | `L & 12 == 0 \|\| c.rf != 2 \|\| pair_ok(..)` in `next_child` |
| `leaf` | `Search::leaf` |
| `explore` | `Search::rec_seq` |
| `kmax` | `kmax` in `Params::new` |
| `oneDigit`, `searchWith`, `search` | `run_search_n` and `max_len`; `search` uses the defaults `--low-digits 3 --low-pairs 2` |

The Lean node stores less than the Rust node. It keeps the counts `cnt` and
the length `pl` of the known prefix. It recomputes `t`, `hi`, `rf`, the
residue and the mask `avail` from `cnt` and the prefix. The Rust code keeps
them as running sums and updates the mask as the prefix grows
(`avail_childAt` shows that its update for a child is right). The Rust code
reads the known prefix from the lanes of `lo`. The Lean code reads it with
`topDigits b d (clo ..) pl`. The last-digit tests read the sum of each
candidate as a number, where the Rust code uses tables of `w(y) mod b^j`.

At level `k`, `cnt x` is the decided count `c_x` for `x >= k`. For `x < k`
it is the number of forced copies of `x`. The tests and their order are the
same as in `next_child`. The search does not use the inexact rules
(`--zscore`, `--cap`, and the others), the parallel split or the journal.

## What is proved

All theorems are in the namespace `Munchausen.ExactSearch`. They use only the
axioms `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no
`native_decide`.

- `search_sound`: every pair `(m, n)` that `search b ms` returns has
  `m` in `ms`, `0 < n` and `IsMunchausen b m n`.
- `mem_search_iff`: for `m` in `ms` with `m <= 1`, the search returns
  `(m, n)` exactly when `n` is a positive solution.
- `found_eq_solutions`: the same as an equality of `Finset`s,
  `found b ms m = solutions b m`.
- `searchWith_sound`, `mem_searchWith_iff`, `foundWith_eq_solutions`: the
  same for `searchWith b ms low pair`, with any numbers `low` and `pair` of
  digits in the last-digit tests (0 turns a test off). `search` is
  `searchWith b ms 3 2`, the Rust default.
- `search_nodup`, `searchWith_nodup`: if `ms` has no duplicates, the search
  returns each pair once.
- `lowDigit_avail_or_free` (Lemma 37.1), `lowOk_of_isCompletion`
  (Proposition 37.2), `pairOk_of_isCompletion` (Proposition 37.4): the
  last-digit tests never prune a node of which a solution is a completion.
- `avail_childAt`: the mask of a child is the mask of its parent, plus the
  digit of the child when the child gives it copies outside the prefix.
- `settle_eq_of_le`: the fuel `d + 1` that the search gives to `settle` is
  enough, so `settle` computes the fixed point of the Rust loop.
- `maxLen_condition_iff`: the Rust length test `d (b-1)^(b-1) >= b^(d-1)`
  holds exactly for `d <= b`, so `max_len` returns `b`. With Proposition 1.1
  (`length_le_maxLen`) the lengths `2` to `b` cover every solution.
- `solutions_two` to `solutions_seven`: the complete lists of positive
  solutions in bases 2 to 7, checked by the kernel with `decide`.

## How the completeness proof works

The proof fixes a solution `n` with `d` digits under `0^0 = m`. It follows
`n` down the tree. `IsCompletion P k N m n` says that `n` is a completion of
the node `N` at level `k`. The decided counts of `N` are the digit counts of
`n`. The forced counts are the counts among the top `pl` digits of `n`. The
known prefix is common to both ends of the interval.

- `root_isCompletion`: the root has the property. Digits above `kmax` have
  count 0 by Proposition 1.2.
- `childAt_isCompletion`: the child with the true count of the next digit
  keeps the property. Its interval lies inside the interval of its parent.
- One lemma per pruning rule shows that the rule spares such a node.
  `t_lt_of_covers` covers the `break` on `lo >= b^d`.
  `pow_le_hi_of_covers` covers the test `hi >= b^(d-1)`.
  `resOk_of_covers` covers the residue rule (Theorem 31.1).
  `lowOk_of_isCompletion` and `pairOk_of_isCompletion` cover the last-digit
  tests on one and two free slots (Propositions 37.2 and 37.4). Both rest on
  `lowDigit_avail_or_free` (Lemma 37.1): a digit of the solution in an
  unknown position is an available digit or a free digit.
  `exists_free_one` and `exists_free_two` name the free digits.
  `settle_isCompletion` covers the forced digits, iterated to a fixed point.
  `firstDigitOk_of_isCompletion` covers the first unknown digit.
- `mem_leaf`: a leaf with the property outputs `(m, n)`.
- `dfs_complete` in `Dfs.lean` composes these steps.

Soundness does not depend on the pruning. The leaf checks each candidate
exactly (`leaf_sound`).

## Differences from the Rust output

- The number 0 is not part of the specification. Mathlib writes 0 with no
  digits, so `IsMunchausen b m 0` always holds. The Rust code prints the
  string `(0)` under `0^0 = 0` only. `rustLine` in `Examples.lean` adds it
  back to compare with the output files.
- The leaf checks only the conventions in `ms`. The Rust leaf checks both,
  and `main.rs` prints the ones in `-m`. The printed output is the same.
- The Lean code computes `t + e w(k) < b^d` before the residue test of child
  `e`. The Rust code tests the residue first. Both orders emit the same
  children.
- The Rust code builds its work units (by default 4 levels) without the
  last-digit tests, so that the units do not depend on them. The Lean tree
  equals the Rust tree of `fast search --unit-depth 0`: the node counts
  agree in bases 2 to 12 (`Examples.lean`).
- The Rust tests need `b <= 64` and take at most 3 and 2 digits. The Lean
  tests take any base and any counts.

## Running it

Build with `lake build Munchausen.Search.Examples`. The `#guard` lines run
the search for bases 2 to 12 and compare the result with the Rust output.
Others compare the node counts with those of
`fast search 2 12 --unit-depth 0 -j 1` for six flag sets, and check that the
solutions do not depend on the digit counts of the last-digit tests.
The kernel checks for bases 2 to 7 take about 30 seconds. A check for base
10 takes about a minute, so it is not in the build.
