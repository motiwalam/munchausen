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

`port`, `reference` and `brute` exist for testing and comparison.

### Options

| option | meaning |
|---|---|
| `-m`, `--mode <0\|1\|both>` | the conventions to report (default `both`) |
| `-j`, `--threads <n>` | number of worker threads (default: one per core) |
| `--journal <file>` | `search` only. Record progress in `<file>`, and resume from it if it exists. `{base}` in the name becomes the base. |
| `--progress` | `search` only. Print progress every 10 seconds. |
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

The search needs only weights that are at least 0. It bounds the free digits
below `k` by the largest weight among the digits up to `k-1`, so the weights
need not increase. A negative `m` lowers the root of the tree by `|m| d`.
Then the program runs the generic path that also serves the inexact rules,
and it needs one more lane per vector. The program searches up to the
largest length `d` with `d * (largest weight) >= b^(d-1)`. That is `b` for
`x^x`, about `b + t` for `x^(x+t)` and about `b - b / ln b` for `x!`. The
GPU path supports only the true weights.

## Speed

The table compares commit `5c3c035` with the current code. Both ran on the
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
`port` with `reference` for bases 2 to 13. For 24 weight options (`--zero`
from -3 to 7, `--shift` from -1 to 3, `--factorial`, `--perturb` with
`--keep-residues` or `--set-residue`), a test compares `search` with a brute
force over all digit multisets in bases 2 to 8. Another test checks the weight
tables. The tests take about 90 seconds.

## Source files

| file | contents |
|---|---|
| `src/search.rs` | the fast search |
| `src/digits.rs` | base-`b` digit vectors in AVX2 registers, with a portable fallback |
| `src/journal.rs` | the journal for resumable runs |
| `src/port.rs` | the port of the Python search |
| `src/reference.rs` | the brute force and the `u128` reference search |
| `src/main.rs` | the command line, output, and tests |
| `src/search/gpu.rs` | the host side of the GPU search |
| `src/vk.rs` | a minimal Vulkan compute context |
| `shaders/search.comp` | the GPU search |
