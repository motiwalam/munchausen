# fast

A Rust program that finds every Munchausen number in bases 2 to 127, up to 62
digits. It searches both conventions for `0^0` in one run. `../docs/algorithm.md`
explains the algorithm, and `../docs/comparison.md` measures it.

## Build

The program needs a stable Rust toolchain with the 2024 edition.

```sh
cargo build --release
```

`.cargo/config.toml` builds for the CPU of the build machine. On a CPU with
AVX2, the program uses AVX2 digit vectors. On other CPUs, it uses plain loops.
The plain loops give the same results and pass the same tests. They are about
4.7x slower: base 25 on one thread takes 4.1 s, against 0.87 s with AVX2.

## Run

```sh
./target/release/fast <engine> <base> [<last base>] [options]
```

For example:

```sh
./target/release/fast search 2 30
./target/release/fast search 36 -m 1
./target/release/fast search 40 --journal 'journal-b{base}.txt' --progress
```

The program writes results to stdout, in the format of `../output/*.txt`. It
writes timings and statistics to stderr. Before it prints a number, it
recomputes the Munchausen sum with arbitrary-precision integers.

### Engines

| engine | what it does | bases |
|---|---|---|
| `search` | the fast search | 2 to 127, at most 62 digits |
| `port` | a line-for-line port of `../src/munchausen.py`, which checks the same combinations | 2 to 26 |
| `reference` | the leading-digit test alone, in `u128` arithmetic | 2 to 27 |
| `brute` | tests every `n` up to `b * (b-1)^(b-1)` | 2 to about 9 |
| `merge` | combines the outputs of `--shard` runs, see "Split a base over processes" | |

`port`, `reference` and `brute` exist for testing and comparison.

### Options

| option | meaning |
|---|---|
| `-m`, `--mode <0\|1\|both>` | the conventions to report (default `both`) |
| `-j`, `--threads <n>` | number of worker threads (default: one per core) |
| `--journal <file>` | `search` only. Record progress in `<file>`, and resume from it if it exists. `{base}` in the name becomes the base. |
| `--progress` | `search` only. Print progress every 10 seconds, with the node count and an estimate of the share of the work done (fitted on bases 26 to 33 under the `x^x` weights, so rough for other weights). |
| `--unit-stats <file>` | `search` only. Write one line per finished work unit: index, digits, `k`, free slots, known digits, start and end seconds, and the node count of the run at the end of the unit (a per-unit count only with `-j 1`). See section 27.5 of the library. |
| `--shard <i>/<n>` | `search` only. Search only the work units whose index is `i` modulo `n`, for `0 <= i < n`. `{shard}` in the journal name becomes `<i>of<n>`. |
| `--max-digits <n>` | `search` only. Look only for numbers with at most `n` digits. Bases above 62 need `n <= 62`. |
| `--min-digits <n>` | `search` only. Look only for numbers with at least `n` digits. |
| `--unit-depth <n>` | `search` only. Tree depth of the resumable work units (default 4). |
| `--par-depth <n>` | `search` only. Depth below a unit at which the program still splits work into parallel tasks (default 4). |

`search` always explores the tree for both conventions. `-m` only selects the
output, so `-m 1` takes as long as `both`.

### Long runs

Each base takes about 1.9x as long as the one before. On the test laptop, base
37 takes 205 seconds with the build of 17 October 2026, so base 40 takes about
25 minutes (an estimate). The first build measured 36 minutes for base 40, on
a machine shared with other jobs (`docs/comparison.md`). Use `--journal` for
long runs. The program appends a line to the journal when a work unit
finishes. It appends another line for each solution, as soon as it finds it.
If a run stops, run the same command again. The program reads the journal and
skips the finished units.

A journal belongs to one base and one value of `--unit-depth`. The program
refuses a journal that does not match.

### Split a base over processes

`--shard i/n` splits a base into `n` parts. Each part runs as its own
process, on the same machine or on different machines. For example, on three
machines:

```sh
./target/release/fast search 40 --shard 0/3 --journal 'j{base}-{shard}.txt' > s0.txt
./target/release/fast search 40 --shard 1/3 --journal 'j{base}-{shard}.txt' > s1.txt
./target/release/fast search 40 --shard 2/3 --journal 'j{base}-{shard}.txt' > s2.txt
```

Then copy the three outputs to one machine and merge them:

```sh
./target/release/fast merge s0.txt s1.txt s2.txt
```

`merge` prints the lines that a single run prints. It fails if the output of
a shard is missing. A shard writes the line `# shard i/n base b` before its
results, and `merge` uses it for this check. The one-digit numbers belong to
shard 0.

Every shard builds the full list of work units and takes every `n`-th unit.
The list is sorted by digit count, so every shard gets its part of each
digit count. For base 30 in 3 shards, the shards visit 22.9, 21.8 and 21.5
million nodes. Each shard also counts the 11,675 nodes that build
the unit list, so the sum of the shard counts is larger than the count of a
single run.

A shard has its own journal, and its header names the shard. Use
`{shard}` in the journal name to keep the files apart. A shard refuses a
journal of another shard.

On one machine, more processes do not help. Base 32 on the test laptop
(4 P-cores and 4 E-cores, other jobs running), median of 5 alternating runs:

| processes x threads | wall time |
|---|---:|
| 1 x 8 | 5.82 s |
| 2 x 4 | 5.98 s |
| 2 x 4, one process pinned to the P-cores and one to the E-cores | 6.67 s |
| 4 x 2 | 6.15 s |
| 8 x 1 | 6.36 s |

One process shares its work between all threads until the end. Fixed
shards cannot. In the pinned run, the shard on the P-cores finished in
4.8 s and the shard on the E-cores in 6.6 s. Use shards to spread a base over
machines, and one process with all threads on each machine.

### Inexact search

These options make `search` skip parts of the tree that the probabilistic
model calls unlikely. The search is then faster but can miss solutions.
`docs/library/9-inexact.md` measures the speed and the miss rates.

| option | the search skips a node if |
|---|---|
| `--cap <c>` | one digit value has more than `c` copies |
| `--band <z>` | the count of digits `>= k` is more than `z` standard deviations from its mean |
| `--deficit <z>` | the known leading digits hold too few digits `>= k`, by more than `z` standard deviations |
| `--ratio <r>` | its expected number of solutions is below `r` times that of its parent |
| `--zscore <z>` | its expected number of solutions is more than `z` standard deviations below the mean for a random suffix |
| `--uniform` | (modifier) use `sqrt(d)/2` as the standard deviation in `--band` and `--deficit` |

With any of these, the program prints the expected number of solutions in the
skipped subtrees. Only `--ratio` and `--zscore` add to this number.
`docs/library/10-limits.md` explains the `--zscore` rule.

These options change the `--zscore` rule:

| option | meaning |
|---|---|
| `--zlaw <poisson\|cond>` | the law of `ln E` that the rule compares with. `poisson` (default) is the law of chapter 10, whose standard deviation is up to 4x too large at the low levels. `cond` conditions the Poisson cells on their total and gets the mean and the standard deviation right. |
| `--zfrom <f>` | the rule applies at the levels `k <= f (kmax + 1)` (default 0.75) |
| `--zslope <s>` | the threshold at level `k` is `z + s (k / (kmax + 1) - 1/2)` (default 0) |
| `--ztable <file>` | replace the law in the cells listed in `<file>`, one line `d k pp mean sd` per cell |

`--zscore 3.4 --zlaw cond` is the best setting so far. It misses about 2%
of model solutions in every base from 30 to 200, and found all 122
solutions of bases 10 to 41. At the same miss rate it visits 1.2x to 1.3x
fewer nodes than `--zscore 2.94` in bases 34 to 42, and takes about 1.1x
less time. For a 1% miss rate, use `--zscore 3.8 --zlaw cond`. Under the
default law, `--zscore 3` misses about 2% at base 30 but only 0.7% at
base 200, so its miss rate depends on the base. A window on the length `d`
does not pay: it saves 1.03x to 1.45x for 2 to 21 points of miss rate,
where a lower threshold saves 1.3x to 6x for the same miss rate.
`docs/library/drafts/round5-performance.md` has the measurements.

Two options measure the tree for these experiments:

| option | output |
|---|---|
| `--zhist <file>` | with `--zscore z`: per length `d`, the nodes and interval evaluations by the smallest z-score on their path. The nodes of `--zscore c` for every `c <= z` are the bins with `z >= -c`, so one run gives the whole curve. |
| `--tree-stats <file>` | per length `d`, level `k` and number `pp` of unknown positions, the number of nodes and their total subtree size |

### Other weights

These options replace the weight `x^x` for experiments on the model. The
program verifies every result with the same weights in arbitrary precision.

| option | weights |
|---|---|
| `--zero <m>` | the digit 0 weighs `m` under the second convention (mode 1); mode 0 keeps 0 |
| `--shift <t>` | `x^(x+t)` for `x >= 1`, with `t >= -1` |
| `--factorial` | `x!` for `x >= 1` |
| `--perturb <seed>` | each weight `w(x)`, `x >= 2`, plus a pseudo-random amount below `w(x)/4` |
| `--keep-residues` | with `--perturb`: the amount is a multiple of `2(b-1)` |
| `--set-residue <r>` | each weight `w(x)`, `x >= 1`, raised by less than `b-1` to make it `x + r` modulo `b-1`, after `--perturb` |
| `--power <p>` | `x^p` for `x >= 1`; with `--zero 0 --min-digits p --max-digits p` the search finds the `p`-digit narcissistic numbers |

The search needs only weights that are at least 0. It bounds the free digits
below `k` by the largest weight among the digits up to `k-1`, so the weights
need not increase. A negative `m` lowers the root of the tree by `|m| d`.
Then the program runs the generic path that also serves the inexact rules,
and it needs one more lane per vector. The program searches up to the
largest length `d` with `d * (largest weight) >= b^(d-1)`. That is `b` for
`x^x`, about `b + t` for `x^(x+t)` and about `b - b / ln b` for `x!`. The
GPU path supports only the true weights.

## Speed

### First round

The table compares commit `5c3c035` with commit `bee1350`. Both ran on the
test laptop in power-saver mode, on the same day, in alternating runs. Each
time is the median of three runs. The node counts are the same in both.

| run | nodes | before | after | speedup |
|---|---:|---:|---:|---:|
| `search 30` | 66,246,690 | 3.54 s | 1.86 s | 1.90x |
| `search 33` | 464,274,849 | 27.7 s | 16.3 s | 1.69x |
| `search 36` | 3,068,291,567 | 181 s | 109 s | 1.66x |
| `search 30 -j 1` | 66,246,690 | 26.2 s | 13.8 s | 1.90x |

Base 30 takes 13.8 s on 1 thread, 3.2 s on 4 and 1.86 s on 8. Up to base 30
a number fits in one 32-byte vector. Bases 31 and up need two, and each
addition then costs about 1.25x as many cycles, so the gain is smaller there.

What helped, measured in cycles for base 26 on one performance core (3.08
billion before, 1.59 billion after):

- No logarithms in the exact search. The model's bookkeeping now runs only
  with `--epsilon` or `--ratio` (8%).
- No 128-byte histogram per node. A vector compare counts the copies of a
  digit in the known prefix (19%).
- The inexact rules are compiled out of the exact search (10%).
- `hi` is updated with one addition per forced digit, and a node keeps its
  `hi` for its children (13% together).
- Work is handed to other threads only when a thread's queue is empty, and
  node counts are kept per thread instead of in shared atomics (10% on one
  thread; with 8 threads the shared counters had cut the IPC from 1.78 to
  1.3).
- An explicit stack replaces the recursion (2%).

### Second round

The table compares commit `7f49357` with the current code. Other jobs shared
the laptop, so the table gives user-mode cycles of one thread pinned to one
core. Each cycle count is the median of two or three alternating runs, and
repeated runs differ by less than 1%. The node counts are the same in both.

| run | nodes | before | after | change |
|---|---:|---:|---:|---:|
| `search 26 -j 1`, P-core | 4,955,060 | 1.598 G | 1.361 G | -14.8% |
| `search 30 -j 1`, P-core | 66,246,690 | 20.66 G | 18.35 G | -11.2% |
| `search 30 -j 1`, E-core | 66,246,690 | 23.44 G | 20.95 G | -10.6% |
| `search 33 -j 1`, P-core | 464,274,849 | 189.2 G | 164.2 G | -13.2% |
| `search 36 -j 1 --min-digits 36`, P-core | 612,827,995 | 255.5 G | 225.3 G | -11.8% |

`search 30` on 8 threads took 1.62 s before and 1.43 s after (median of 5
alternating runs, load average 2 to 4 from other jobs). At bases 33 and 36
the other jobs kept the load average at 6 to 14, and the wall times varied
by 30% between runs of the same binary.

What helped:

- About one branch per child mispredicts, and a mispredict throws away the
  work after it. The sums `t` and `hi` of child `e + 1` are now computed
  before the tests of child `e` (8.3% at base 26).
- The sums of the forced digits are added before the check of the new digits
  `>= k`, whose loop exit mispredicts often (1.6%).
- A node stores the `hi` of its first child. The addition that makes it now
  runs before the first-digit test, not after it (4.7%).
- A cursor no longer copies the sums of its node (0.9%).

What did not help, in cycles at base 26 on a P-core:

- `te` and `hi` from tables of multiples instead of running sums: 1.598 G
  became 1.728 G.
- The digits `>= k` checked two at a time, to make the loop exit easier to
  predict: no fewer branch misses, 1.4% more cycles.
- The first forced digit and the first-digit test without branches: 0.3%
  and 2.4% more cycles.
- Evaluations counted once per cursor instead of once per child: 1.5% more
  cycles.
- A 128-bit upper word for two-word vectors (bases 31 to 46). A prototype
  gained 1.7% on an E-core and lost 4.5% on a P-core. Two words cost 1.26x
  the cycles of one word on a P-core and 1.32x on an E-core, so a half-width
  word can win at most the difference on E-cores.
- The leaf. It runs 3 to 10 times per base (10 times at base 30, for 66
  million nodes), and none of 56,501 samples at base 27 fell in it.
- Exact cuts in the loop over `e`, see "The loop over e" in
  `../docs/algorithm.md`.

`docs/algorithm.md` describes the data structures.

## GPU search

With `--features gpu`, the program can run the search on a GPU
through Vulkan 1.3. The build needs `glslc` (from shaderc) to compile
`shaders/search.comp`. The default build does not use the GPU.

```sh
cargo build --release --features gpu
./target/release/fast search 32 --gpu
./target/release/fast search 32 --hybrid
```

`--gpu` runs every unit on the GPU. `--hybrid` also runs units on the CPU
threads. Both give the same solutions and the same node counts as the CPU
search. A test checks this for bases 2 to 26. The GPU path runs the exact
search and the `--zscore` rule, with `--zlaw`, `--zfrom`, `--zslope` and
`--ztable`. It accepts `--shard` and `--min-digits`/`--max-digits`, but not
`--journal`, the other inexact rules, or other weights. It handles bases
up to 64. The GPU tests the rule in fixed point with 20 fractional bits.
A test checks that it visits the same nodes as the CPU for bases 10 to 26,
and runs at bases 28, 30 and 33 gave the same node counts too. The
expected number of solutions in skipped subtrees counts only the nodes that
the CPU skipped.

### How it works

One subgroup of 32 lanes runs one depth-first search. It plays the part
of an AVX2 register: lane `l` holds digit `l` (or digits `l` and `l + 32`
above 30 digits), and a ballot replaces movemask. Every branch depends on
values that are the same in all lanes, so the lanes never diverge. The
lanes also hold a histogram of the known leading digits, so a count check
is one compare and one ballot.

The `xe` driver kills a GPU job after 5 seconds. So each subgroup stops
after a node budget per dispatch, about 0.25 s of work, and writes every
pending cursor of its stack back as a new work item. Large subtrees split
by themselves. With `--hybrid`, the CPU threads take units and these
cursors from the same pool.

### Speed

On the test laptop (Arc 140V GPU, power-saver mode), after the second
round of CPU speedups. Each time is the median of 5 interleaved runs (3
for base 33). Other jobs shared the machine: the 1-minute load was 7.6 to
10, so the CPU times are slower than on an idle machine.

| base | nodes | CPU, 8 threads | `--gpu` | `--hybrid` |
|---|---:|---:|---:|---:|
| 30 | 66,246,690 | 1.34 s | 0.95 s | 0.83 s |
| 32 | 214,709,067 | 5.24 s | 4.33 s | 3.09 s |
| 33 | 464,274,849 | 10.9 s | 9.6 s | 6.1 s |

The GPU spends about 0.15 s on setup, so it loses on small bases: before
the CPU speedups, base 26 took 0.25 s on the GPU and 0.22 s on the CPU.
Above 30 digits, each lane holds two digits, and the GPU visits about 48
million nodes per second instead of 62 million. `--hybrid` is the fastest
mode in every base measured from 30 up.

With the `--zscore` rule, a later round measured base 38 under a load of 7
to 14 from other jobs (median of 2 or 3 alternating runs):

| run | CPU, 8 threads | `--gpu` | `--hybrid` |
|---|---:|---:|---:|
| `search 34` (exact) | 34.1 s | 20.3 s | 13.2 s |
| `search 38 --zscore 3` | 74.4 s | 43.9 s | 28.3 s |
| `search 38 --zscore 3.4 --zlaw cond` | 70.5 s | 37.0 s | 24.7 s |

The load slows the CPU threads more than the GPU, so these ratios are
larger than on an idle machine. With the rule the GPU visits 24 to 27
million nodes per second.

What limits it: not divergence, and not memory. Each subgroup runs a long
chain of dependent instructions. Values that are the same in all lanes
still take a full 32-lane instruction. With one subgroup per vector engine,
base 30 takes 4.2 s; with eight it takes 1.19 s, only 3.6 times faster.
Subgroups of 16 lanes with two digits each were slower.

## kdigit: short solutions in all bases

`kdigit <k> <M>` finds every `k`-digit solution, in every base, whose
digits are at most `M`. It is complete for the bases `b` with
`b^k <= (M+1)^(M+1)`. It discards the strings whose polynomial `Q_s` has
no root modulo some modulus, and solves the rest exactly
(`../docs/library/11-local.md`, section 11.5, and
`../docs/library/drafts/round3-computation.md`, section 47).

| option | meaning |
|---|---|
| `--survivors` | print the strings that pass the test instead of the solutions |
| `--offset <D>` | find the strings with `P_s(b) - F(s) = D` in place of 0 |
| `--moduli <q1,q2,...>` | the moduli of the test, each from 2 to 128, in the order they are tried (default 32, 27, 25, 49 and the primes 11 to 127) |
| `--stats` | print, per modulus, how many candidates it tests and removes |

The thread count comes from `RAYON_NUM_THREADS`.

## Test

```sh
cargo test --release
```

The tests compare `search` with `brute` for bases 2 to 9 and with `reference`
for bases 10 to 22. They test both widths of digit vectors. They also compare
`port` with `reference` for bases 2 to 13. They check that 2, 3 and 7 shards
together find what one run finds. For 24 weight options (`--zero` from -3 to
7, `--shift` from -1 to 3, `--factorial`, `--perturb` with `--keep-residues`
or `--set-residue`), a test compares `search` with a brute force over all
digit multisets in bases 2 to 8. Another test checks the weight tables. The
tests take about 90 seconds.

## Source files

| file | contents |
|---|---|
| `src/search.rs` | the fast search |
| `src/digits.rs` | base-`b` digit vectors in AVX2 registers, with a portable fallback |
| `src/journal.rs` | the journal for resumable runs |
| `src/merge.rs` | the `merge` command for the outputs of shards |
| `src/port.rs` | the port of the Python search |
| `src/reference.rs` | the brute force and the `u128` reference search |
| `src/main.rs` | the command line, output, and tests |
| `src/search/gpu.rs` | the host side of the GPU search |
| `src/vk.rs` | a minimal Vulkan compute context |
| `shaders/search.comp` | the GPU search |
