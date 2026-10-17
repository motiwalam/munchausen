# Comparing the approaches

This document compares the ways to search for Munchausen numbers. It covers
the approaches in this repository and the published searches by other
people. `docs/algorithm.md` explains the algorithms.

## Measurement setup

All timings in this repository come from one laptop: an Intel Core Ultra 7
258V with 4 performance cores and 4 low-power cores. During every run the
laptop ran on battery in power-saver mode, so the cores ran at about 1.7 GHz.

Under these conditions, the same command can run up to 2x faster or slower
from one run to the next. For this reason, the tables below lead with work
counts, which are exact and machine-independent. Timings come second.

The approaches are:

| name | what it is |
|---|---|
| python | `src/munchausen.py` under PyPy 3.11, 8 processes |
| port | `fast port`, a line-for-line Rust port of the python search, 8 threads |
| reference | `fast reference`, leading-digit test only, `u128` integers, 1 thread |
| fast | `fast search`, the full algorithm with digit vectors, 1 or 8 threads |

Python, port and reference search one convention per run. `fast` searches
both conventions in one run, and every `fast` number below covers both.

## Work per base

Each column counts the candidates that an approach examines.

- "numbers": every `n` up to the bound `2 * b^b`, as a brute force tests them.
- "multisets": every digit multiset with 2 to `b+1` digits (`nb1` in
  `src/nb.py`).
- "python": the combinations that `gcwr` generates (`nb7`, which matches the
  port's count exactly).
- "fast": the intervals that the leading-digit test evaluates, and the tree
  nodes that pass.

| base | numbers | multisets | python | fast: intervals | fast: nodes |
|---:|---:|---:|---:|---:|---:|
| 10 | 2.0e10 | 352,705 | 43,610 | 819 | 265 |
| 16 | 3.7e19 | 1.2e9 | 142,320,542 | 32,093 | 9,793 |
| 19 | 4.0e24 | 6.9e10 | 8.3e9 | 202,602 | 60,996 |
| 20 | 2.1e26 | 2.7e11 | 3.2e10 | 373,837 | 111,460 |
| 25 | 1.8e35 | 2.5e14 | 3.0e13 | 8,835,470 | 2,662,771 |
| 30 | 4.1e44 | 2.3e17 | 2.8e16 | 232,181,518 | 71,430,962 |
| 35 | 2.2e54 | 2.2e20 | 2.6e19 | 5,326,689,044 | 1,611,838,947 |
| 38 | 2.2e60 | 1.4e22 | 1.6e21 | not recorded | not recorded |

The python search examines about 8 times fewer candidates than the full
multiset count: 8.1x at base 10 and 8.5x at base 38.

Against python, the `fast` search examines 41,000 times fewer candidates at
base 19. The factor is 3.4 million at base 25 and 4.9 billion at base 35.

The gap grows because the two approaches grow at different rates:

| approach | growth per base | source |
|---|---:|---|
| multisets | 4.0x | `C(2b, b)` |
| python | 3.9x | `nb7`, bases 19 to 38 |
| fast | 1.9x | intervals, bases 30 to 35 |
| fast, time | 1.9x | bases 35 to 38: 77 s, 146 s, 277 s, 520 s |

## Effect of each pruning rule

The counts below come from an early `u128` prototype of the `fast` search. They
are tree nodes for the `0^0 = 1` convention only.

| base | leading digits | + forced digits | + feasibility check |
|---:|---:|---:|---:|
| 19 | 158,036 | 61,067 | 53,268 |
| 21 | 548,543 | 198,015 | 175,360 |
| 23 | 2,204,307 | 763,048 | 682,607 |

- The leading-digit test alone is the `reference` engine.
- Forced digits cut the tree by a factor of 2.6 to 2.9. The `fast` search uses
  them.
- The feasibility check asked whether any number in `[lo, hi]` can be
  arranged from the remaining digits. It removed another 10 to 13 percent of
  the nodes. The `fast` search does not include it yet.

Searching both conventions at once costs almost no extra work. For base 28, a
run for `0^0 = 1` alone visited 19,361,945 nodes. A run for both conventions
visited 19,362,129.

## Where the work goes

By number of digits. These are the interval counts for base 28, one
convention, 62,785,212 in total:

| digits | share |
|---:|---:|
| 28 (`d = b`) | 16.4% |
| 27 | 52.1% |
| 26 | 20.9% |
| 25 | 6.6% |
| 24 | 1.9% |
| 2 to 23 | 2.2% |

A proof that no `b`-digit Munchausen number exists for `b > 2` would skip the
first row and save about 16% of the time. Under `0^0 = 1`, no base from 3 to
38 has a `b`-digit solution. Under `0^0 = 0`, bases 15 and 16 each have one,
so there the statement is false.

By depth. For base 27, 82% of the 33,204,174 intervals belong to the digits 13
to 19, the middle of the tree. The digits 2 to 6 account for 8,549 intervals.
Shortcuts at the leaves therefore cannot save much time.

By outcome. For the same base 27 run:

| outcome | intervals | share |
|---|---:|---:|
| fails the leading-digit test | 23,006,638 | 69.3% |
| passes, with new leading digits | 8,992,523 | 27.1% |
| passes, no new leading digits | 1,204,898 | 3.6% |
| outside the range of `d`-digit numbers | 115 | 0.0% |

## Timings

All runs use the setup described above. An empty cell means that the run was
too slow to try, or that it was not measured.

| base | python | port | reference | fast, 1 thread | fast, 8 threads |
|---:|---:|---:|---:|---:|---:|
| 14 | | 0.39 s | | | |
| 15 | | 1.38 s | | | |
| 16 | 131 s | 5.98 s | 0.089 s | 0.006 s | 0.007 s |
| 17 | | 24.6 s | | | |
| 18 | | 109 s | | | |
| 19 | | | 0.65 s | 0.054 s | 0.031 s |
| 20 | | | | 0.047 s | 0.035 s |
| 22 | | | 5.81 s | 0.155 s | 0.098 s |
| 25 | | | 57.9 s | 0.85 s | 0.30 s |
| 28 | | | | 5.85 s | 1.19 s |
| 30 | | | | 21.0 s | 2.94 s |
| 35 | | | | | 77 s |
| 36 | | | | | 146 s |
| 37 | | | | | 277 s |
| 38 | | | | | 520 s |
| 39 | | | | | 19 min |
| 40 | | | | | 36 min |
| 41 | | | | | 59 min |

Bases 39 to 41 ran while other analysis jobs shared the machine, so their
times are somewhat high.

The `fast` columns above predate the performance work in `fast/README.md`
("Speed"). That work changed constant factors only, and the node counts
stayed the same. The machine also runs slower on some days than on others.
So the comparison below ran both builds on the same day, in alternating
runs, and gives the median of three:

| run | before | after |
|---|---:|---:|
| base 30, 1 thread | 26.2 s | 13.8 s |
| base 30, 4 threads | 6.14 s | 3.19 s |
| base 30, 8 threads | 3.54 s | 1.86 s |
| base 33, 8 threads | 27.7 s | 16.3 s |
| base 36, 8 threads | 181 s | 109 s |
| base 37, 8 threads | | 205 s |

On that day the old build took 181 s for base 36, against the 146 s in the
table above.

The original README gave 169 s for python at base 16 and about 17 hours at
base 19, from a different machine.

### What each change bought

- Language. The port checks the same 142,320,542 combinations as python for
  base 16. It runs at 23.8 million combinations per second, against 1.09
  million for PyPy. That is a factor of 22.
- Algorithm. At base 25 the reference engine visits 7,535,030 nodes. Python
  would examine 3.0e13 combinations. At the port's rate that is about 14 days.
  The reference engine takes 58 seconds.
- Forced digits and digit vectors. At base 25, `fast` on one thread visits
  2,662,771 nodes in 0.85 s, or 3.1 million nodes per second. The reference
  engine manages 130,000 nodes per second, and it covers one convention. So
  `fast` does 24x more nodes per second and visits 2.8x fewer nodes.
- Digit vectors alone. The same code built without AVX2, with plain loops in
  place of vector instructions, takes 4.1 s for base 25 on one thread. The
  AVX2 build takes 0.87 s, so the vectors are worth 4.7x.
- Threads. On 8 threads, `fast` ran 4.9x faster at base 28 and 7.2x faster
  at base 30. The changing clock speed affects these ratios too. At base 29,
  an earlier build ran 3.8x faster on 4 threads and 4.6x faster on 8. The low-power cores give about 57% of the throughput of a
  performance core. Small bases finish before the threads are busy.

For comparison, the python search at base 38 would examine 1.6e21
combinations. At the port's rate that is about 2 million years. `fast` takes
520 seconds.

### Cost of one interval

Valgrind measured a single-threaded base 22 run, which evaluates 1,361,059
intervals:

- 319.6 million instructions in total, about 235 per interval,
- 3,486,038 simulated branch mispredictions, about 2.6 per interval,
- 86 ns per interval in a normal run, at about 1.7 GHz.

That is about 146 cycles and 1.6 instructions per cycle for each interval. One
digit-vector addition takes about 15 instructions, and each interval needs two
to four additions. Most of the remaining instructions update the digit counts
and handle the branches.

After the performance work, a base 26 run on one performance core evaluates
16,313,626 intervals in 1.59 billion cycles and 3.15 billion instructions.
That is 97 cycles, 193 instructions and 1.0 branch mispredictions per
interval, measured with the hardware counters. The two additions per
interval take about 30% of the time.

## Other published searches

These figures come from the cited sources. Their hardware is not comparable
with the laptop above, and most sources do not state it.

| search | language and method | bases | reported time |
|---|---|---|---|
| van Berkel, [arXiv 0911.3038](https://arxiv.org/abs/0911.3038), 2009 | GAP, every `n` up to `2 * b^b` | 2 to 10 | not stated |
| Karl W. Heuer, OEIS [A166623](https://oeis.org/A166623), 2011 | method not published | 2 to 35, `0^0 = 1` | not stated |
| Elizarov, [MunchausenNumbers](https://github.com/elizarov/MunchausenNumbers), 2016 | Kotlin, meet in the middle per digit count, with a bitset of reachable sums modulo a large number | 2 to 16, `0^0 = 1` | base 15 about 10 min, base 16 about 5.5 h |
| Goulu, [gist](https://gist.github.com/goulu/5121c161d224229b76a38485c4122794) | Python | 2 to 16, `0^0 = 0` | base 15 4 h 11 min, base 16 4.8 days; misses some numbers |
| Matthew, [Programming Praxis](https://programmingpraxis.com/2019/12/06/muenchhausen-numbers/), 2019 | C++, all digit combinations, compare sorted digits | up to 16 | base 16 about 40 s |
| Daniel, same thread, 2020 | C++ with GMP, OpenMP on 16 threads, combination unranking | 17 to 20 | base 19 91 min, base 20 334 min |
| this repository, python | PyPy, `gcwr` | 2 to 19 | base 16 131 s, base 19 about 17 h |
| this repository, `fast` | Rust, prefix-pruned counts, AVX2 digit vectors | 2 to 41, both | base 20 0.035 s, base 35 77 s, base 38 520 s, base 41 59 min |

I found no published search beyond base 35. For `0^0 = 0`, I found no
published list beyond about base 17. Bases 36 to 41 were not searched before, under either
convention.

## Ideas that are not built yet

| idea | expected effect | evidence |
|---|---|---|
| port the feasibility check | 10 to 13 percent fewer nodes | prototype counts above |
| prove that no `b`-digit solution exists under `0^0 = 1` | about 16 percent less time | share of `d = b` at base 28 |
| 48-lane vectors (32 + 16 bytes) for bases 31 to 46 | fewer vector instructions than two full registers | not measured |
| split the work units over several machines | linear in the number of machines | the units are independent, but this is not measured |

None of these ideas changes the growth rate of about 1.9x per base. At that
rate, and on the laptop above, base 40 takes about 30 minutes, base 45 about
13 hours, and base 50 about 13 days.

Chapter 6 of `docs/library/` explains where the growth comes from. It also
covers the meet-in-the-middle and lattice approaches that I examined and that
do not lower it.
