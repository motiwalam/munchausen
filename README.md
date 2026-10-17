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
measured numbers.

## Layout

| path | contents |
|---|---|
| `fast/` | the Rust search, a Rust port of the Python search, and two reference searches for testing |
| `src/munchausen.py` | the Python search |
| `src/common.py` | helpers for the Python search, including the `testbd0` pre-check |
| `src/nb.py` | the size of the search space after each Python optimization |
| `src/formatutil.py` | reads and writes the output format |
| `output/` | results |
| `docs/` | algorithm and comparison documents |

## Open questions

The long-term goal is to understand Munchausen numbers well enough to answer
these questions:

- Can we find the Munchausen numbers of a base in polynomial time?
- Do Munchausen numbers have a general form?
- Can we predict how many Munchausen numbers a base has?

An exhaustive search cannot keep up with the growth forever. At 1.9x per base,
base 45 takes about 13 hours on the test laptop and base 50 about 13 days.
Answers to these questions need a better understanding of the numbers
themselves, for example a way to construct them directly.

### Conjecture: no `b`-digit Munchausen numbers for `b > 2`

In base 2, `10` (that is, 2) is a 2-digit Munchausen number under `0^0 = 1`.
The conjecture says that this is the only case with `b` digits. The results
agree: in bases 3 to 38, no solution has `b` digits under either convention.

A proof would let both searches skip the `b`-digit case. That is 26% of the
combinations in the Python search, and 16% of the work in the Rust search at
base 28.

Notes towards a proof:

- The largest Munchausen sum of a `b`-digit number is `b * (b-1)^(b-1)`. This
  is less than `b^b`.
- The leading digit of `b * (b-1)^(b-1)` in base `b` is about `b / e`.
- For `b > 2`, a `b`-digit Munchausen number must contain the digit `b-1` 3
  times.
