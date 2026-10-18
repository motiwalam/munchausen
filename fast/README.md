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
| `--progress` | `search` only. Print progress every 10 seconds. |
| `--shard <i>/<n>` | `search` only. Search only the work units whose index is `i` modulo `n`, for `0 <= i < n`. `{shard}` in the journal name becomes `<i>of<n>`. |
| `--max-digits <n>` | `search` only. Look only for numbers with at most `n` digits. Bases above 62 need `n <= 62`. |
| `--min-digits <n>` | `search` only. Look only for numbers with at least `n` digits. |
| `--unit-depth <n>` | `search` only. Tree depth of the resumable work units (default 4). |
| `--par-depth <n>` | `search` only. Depth below a unit at which the program still splits work into parallel tasks (default 4). |

`search` always explores the tree for both conventions. `-m` only selects the
output, so `-m 1` takes as long as `both`.

### Long runs

Each base takes about 1.9x as long as the one before. On the test laptop,
base 37 takes 205 seconds, so base 40 takes about 25 minutes. Use `--journal`
for long runs. The program appends a line to the journal when a work unit
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
`--zscore 3` is the best setting so far. It grows about 1.75x per base, found
all 112 solutions in bases 10 to 38, and misses 1 to 3% of model solutions in
every base from 30 to 300. `docs/library/10-limits.md` explains the rule.

Two options exist for experiments on the model. `--perturb <seed>` adds a
random amount of up to a quarter to each weight `x^x`. `--keep-residues`
rounds that amount to a multiple of `2(b-1)`. With `--perturb` the program
does not verify its results, because they are not Munchausen numbers.

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

With `--features gpu`, the program can run the exact search on a GPU
through Vulkan 1.3. The build needs `glslc` (from shaderc) to compile
`shaders/search.comp`. The default build does not use the GPU.

```sh
cargo build --release --features gpu
./target/release/fast search 32 --gpu
./target/release/fast search 32 --hybrid
```

`--gpu` runs every unit on the GPU. `--hybrid` also runs units on the CPU
threads. Both give the same solutions and the same node counts as the CPU
search. A test checks this for bases 2 to 26. The GPU path supports only
the exact search, without `--journal`.

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

On the test laptop (Arc 140V GPU, power-saver mode), the median of 5
interleaved runs. Other jobs shared the machine: the 1-minute load was
9.5 to 14, so the CPU times are slower than in the table above.

| base | nodes | CPU, 8 threads | `--gpu` | `--hybrid` |
|---|---:|---:|---:|---:|
| 26 | 4,955,060 | 0.22 s | 0.25 s | 0.19 s |
| 28 | 18,025,432 | 0.67 s | 0.41 s | 0.43 s |
| 30 | 66,246,690 | 1.98 s | 1.06 s | 0.90 s |
| 32 | 214,709,067 | 7.42 s | 4.60 s | 3.11 s |
| 33 | 464,274,849 | 12.1 s | 9.6 s | 6.2 s |

Base 33 is one run each. The GPU spends about 0.15 s on setup, so it
loses below base 27. Above 30 digits, each lane holds two digits, and the
GPU visits about 48 million nodes per second instead of 62 million.

What limits it: not divergence, and not memory. Each subgroup runs a long
chain of dependent instructions. Values that are the same in all lanes
still take a full 32-lane instruction. With one subgroup per vector engine,
base 30 takes 4.2 s; with eight it takes 1.19 s, only 3.6 times faster.
Subgroups of 16 lanes with two digits each were slower.

## Test

```sh
cargo test --release
```

The tests compare `search` with `brute` for bases 2 to 9 and with `reference`
for bases 10 to 22. They test both widths of digit vectors. They also compare
`port` with `reference` for bases 2 to 13. They check that 2, 3 and 7 shards
together find what one run finds. The tests take about 90 seconds.

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
