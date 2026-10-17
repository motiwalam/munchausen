# munchausen

An exhaustive search for Munchausen numbers in every base from 2 to 38.

## The problem

Write `n` in base `b`, raise each digit to its own power, and add the results.
This gives the Munchausen sum `F(n, b)`. A Munchausen number in base `b` is a
number with `F(n, b) = n`.

Two examples:

- Base 10: `3435 = 3^3 + 4^4 + 3^3 + 5^5`.
- Base 17: `54` is `33` in base 17, and `3^3 + 3^3 = 54`.

## The two conventions for `0^0`

`0^0` has no agreed value. Ignoring every number that contains the digit 0
throws away too much. So the search supports both common choices, `0^0 = 0`
and `0^0 = 1`.

If you treat `0^0` as undefined, drop the numbers that contain a 0. This works
in one direction only. You cannot rebuild the other two lists from that one.

## Results

`output/b2-38-0.txt` (`0^0 = 0`) and `output/b2-38-1.txt` (`0^0 = 1`) list
every Munchausen number in bases 2 to 38. Each line has the form
`base:convention:count: numbers`. Each number is a tuple of its digits, most
significant first, with the digits written in decimal. `src/formatutil.py`
reads and writes this format. `output/b2-19-*.txt` hold the older results of
the Python search, and the new files agree with them.

Every base has the trivial solution 1, and `0^0 = 0` also has 0. The table
counts the other solutions:

| base | `0^0 = 0` | `0^0 = 1` | | base | `0^0 = 0` | `0^0 = 1` |
|---:|---:|---:|---|---:|---:|---:|
| 2 | 0 | 1 | | 21 | 1 | 2 |
| 3 | 2 | 2 | | 22 | 1 | 1 |
| 4 | 3 | 2 | | 23 | 1 | 0 |
| 5 | 2 | 0 | | 24 | 1 | 1 |
| 6 | 2 | 2 | | 25 | 5 | 2 |
| 7 | 1 | 1 | | 26 | 1 | 2 |
| 8 | 2 | 0 | | 27 | 0 | 0 |
| 9 | 6 | 3 | | 28 | 0 | 3 |
| 10 | 2 | 1 | | 29 | 1 | 0 |
| 11 | 5 | 2 | | 30 | 0 | 1 |
| 12 | 1 | 1 | | 31 | 3 | 2 |
| 13 | 5 | 4 | | 32 | 4 | 0 |
| 14 | 1 | 4 | | 33 | 3 | 2 |
| 15 | 7 | 5 | | 34 | 1 | 1 |
| 16 | 4 | 2 | | 35 | 0 | 0 |
| 17 | 4 | 4 | | 36 | 0 | 1 |
| 18 | 2 | 3 | | 37 | 3 | 3 |
| 19 | 0 | 0 | | 38 | 2 | 3 |
| 20 | 2 | 2 | | | | |

How these results relate to earlier work:

- For `0^0 = 1`, bases 2 to 35 match OEIS [A166623](https://oeis.org/A166623)
  exactly. That table comes from one search by Karl W. Heuer in 2011, with an
  unpublished method.
- For `0^0 = 0`, I found no published list beyond about base 17.
- I found no published search of bases 36 to 38 under either convention.

## Running the search

The Rust search in `fast/` is the one to use. It needs a stable Rust
toolchain.

```sh
cd fast
cargo build --release
./target/release/fast search 2 30
./target/release/fast search 40 --journal 'journal-b{base}.txt' --progress
```

The first command searches bases 2 to 30 under both conventions. The second
command searches base 40 and records its progress in a journal file. If that
run stops, run the same command again, and it continues where it stopped.
`fast/README.md` lists every option.

The original Python search is in `src/`. It needs PyPy and the `pathos`
package:

```sh
cd src
pypy3 munchausen.py 2 16 1
```

The arguments are the first base, the last base, and the value of `0^0`.

## How the search works

A Munchausen number has at most `b` digits. Its sum depends only on how many
times each digit appears, so both searches enumerate digit counts in place of
numbers.

- The Python search generates digit combinations and skips groups that
  cannot reach the right number of digits. Its work grows about 3.9x per
  base. Base 16 takes 131 seconds and base 19 about 17 hours.
- The Rust search fixes the count of the largest digit first, then the next
  one, and so on. After each step, the sum lies in an interval. Every number
  in the interval starts with the same digits, and the digit counts must
  allow those digits. Most branches fail this test after a few steps. The
  work grows about 1.9x per base. Base 20 takes 0.035 seconds and base 38
  takes 520 seconds.

`docs/algorithm.md` explains both searches in detail, with a worked example.
`docs/comparison.md` compares them, and other published searches, with
measured numbers. `docs/library/` covers the mathematics.

## Layout

| path | contents |
|---|---|
| `fast/` | the Rust search, a Rust port of the Python search, and two reference searches for testing |
| `src/munchausen.py` | the Python search |
| `src/common.py` | helpers for the Python search, including the `testbd0` pre-check |
| `src/nb.py` | the size of the search space after each Python optimization |
| `src/formatutil.py` | reads and writes the output format |
| `output/` | results |
| `docs/` | the search algorithm, the comparison of approaches, and `docs/library/`, the mathematics |
| `analysis/` | the scripts and data behind every number in `docs/library/` |

## What we know

`docs/library/` is a set of notes on the mathematics, with proofs, complete
tables of short solutions, a probabilistic model, and open problems. The main
points:

- Large-base Munchausen numbers behave like coincidences. A probabilistic model
  predicts about one nontrivial solution per base and convention, most often
  with `b-1` digits. Odd bases have twice as many under `0^0 = 0`, because
  `x^x` and `x` always have the same parity.
- Some solutions need no search. A digit `a` with `a^(a-1) = b^k` pays for
  itself at position `k`, which gives `513` in base 25, `400` in base 8, and
  families in every suitable perfect-power base. Two digits can also pay for
  each other, as in `(3, 0, 27)` in base `3^40`.
- Every 2-digit solution is known: `(a, c)` works exactly when `a` divides
  `c^c - c`, in one base determined by `a` and `c`.
- Under `0^0 = 0` every length occurs in infinitely many bases, and a single
  base can have arbitrarily many solutions. Under `0^0 = 1` short solutions
  look finite: there are exactly two 4-digit solutions (3435 in base 10 and
  `(6,5,3,4)` in base 20) in all bases up to `10^18`, and no base up to 127
  has a 9-digit solution.
- The exhaustive search costs about `1.87^b`. I found no exact method that
  grows more slowly, so a complete search of base 100 is out of reach. Base 100
  has no nontrivial solution with 50 digits or fewer.

## Open questions

The long-term goal is to understand Munchausen numbers well enough to answer
these questions:

- Can we find the Munchausen numbers of a base in polynomial time? Chapter 6
  of the library explains why the known approaches stay exponential.
- Do Munchausen numbers have a general form? Only the families of chapter 2.
  The solutions near `b` digits show no structure.
- Can we predict how many Munchausen numbers a base has? On average, yes:
  about one per convention for large bases. The exact count of a single base
  looks random.

`docs/library/7-open.md` lists the conjectures with their evidence.

### Conjecture: no `b`-digit Munchausen numbers for `b > 2`

In base 2, `10` (that is, 2) is a 2-digit Munchausen number under `0^0 = 1`.
The conjecture says that this is the only case with `b` digits.

Under `0^0 = 0` the conjecture is false. Base 15 has the 15-digit solution
`(1,2,4,3,14,14,13,3,4,1,9,1,1,0,14)`, and base 16 has the 16-digit solution
`(1,2,3,11,2,3,0,9,15,15,5,7,2,15,6,11)`. Both are in `output/b2-19-0.txt`.

Under `0^0 = 1` the conjecture holds for bases 3 to 40. The probabilistic
model expects a `b`-digit solution in about 1 base in 12, so I expect it to
fail in some larger base.

A proof would let both searches skip the `b`-digit case. That is 26% of the
combinations in the Python search, and 16% of the work in the Rust search at
base 28.

Facts about `b`-digit solutions:

- The largest Munchausen sum of a `b`-digit number is `b * (b-1)^(b-1)`. This
  is less than `b^b`.
- The leading digit of `b * (b-1)^(b-1)` in base `b` is about `b / e`.
- For `b >= 7`, a `b`-digit Munchausen number contains the digit `b-1` at
  least 3 times (Proposition 1.6 in the library). Both counterexamples above
  contain it exactly 3 times.
