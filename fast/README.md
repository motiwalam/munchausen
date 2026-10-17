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
base 38 took 520 seconds, so base 40 takes about 30 minutes. Use `--journal`
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
| `--uniform` | (modifier) use `sqrt(d)/2` as the standard deviation in `--band` and `--deficit` |

With any of these, the program prints the expected number of solutions in the
skipped subtrees. Only `--ratio` adds to this number.
`--deficit 2 --band 2.5` grows about 1.71x per base and misses about 5 to 20%
of solutions between base 30 and base 100.

Two options exist for experiments on the model. `--perturb <seed>` adds a
random amount of up to a quarter to each weight `x^x`. `--keep-residues`
rounds that amount to a multiple of `2(b-1)`. With `--perturb` the program
does not verify its results, because they are not Munchausen numbers.

## Test

```sh
cargo test --release
```

The tests compare `search` with `brute` for bases 2 to 9 and with `reference`
for bases 10 to 22. They test both widths of digit vectors. They also compare
`port` with `reference` for bases 2 to 13. The tests take about 90 seconds.

## Source files

| file | contents |
|---|---|
| `src/search.rs` | the fast search |
| `src/digits.rs` | base-`b` digit vectors in AVX2 registers, with a portable fallback |
| `src/journal.rs` | the journal for resumable runs |
| `src/port.rs` | the port of the Python search |
| `src/reference.rs` | the brute force and the `u128` reference search |
| `src/main.rs` | the command line, output, and tests |
