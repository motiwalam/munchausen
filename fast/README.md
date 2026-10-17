# fast: a Rust search for Munchausen numbers

An exhaustive search for Munchausen numbers (perfect digit-to-digit invariants)
in bases 2 to 62. It handles both conventions for `0^0` in a single pass.

## Build and run

Requires a Rust toolchain (stable, 2024 edition). `.cargo/config.toml` builds for
the native CPU, so the AVX2 code path is used where available. Other CPUs get a
portable fallback that gives the same results more slowly.

```sh
cargo build --release
./target/release/fast search 2 30                 # bases 2..=30, both conventions
./target/release/fast search 36 -m 1 --progress   # one base, 0^0 = 1 only
./target/release/fast search 40 --journal 'journal-b{base}.txt' --progress
cargo test --release                              # cross-check against the reference engines
```

Results go to stdout in the same format as `../output/*.txt` (`base:mode:count: tuples`).
Before anything is printed, each number is re-checked with arbitrary-precision arithmetic.

`--journal` makes a long run resumable. The search is cut into a deterministic
list of work units. Each finished unit and each solution is appended to the
journal as soon as it happens. Rerunning the same command after an interruption
skips the units that are already done.

### Other engines

These are kept for validation and comparison:

| engine      | what it is |
|-------------|------------|
| `port`      | Faithful port of `../src/munchausen.py`. It enumerates exactly the same digit combinations (`gcwr` + `testbd0`), so it measures the language change alone. |
| `reference` | The core idea of `search` in plain `u128` arithmetic, without the refinements. Bases up to 27. |
| `brute`     | Evaluates every `n` up to `b·(b-1)^(b-1)`. Bases up to about 9. |

## Algorithm

The Munchausen sum `F(n)` depends only on the multiset of digits. So for each
number of digits `d` (2 to `b`; more digits are impossible), the search picks
digit *counts* `c_{b-1}, c_{b-2}, ..., c_1` from the largest digit down.

**Leading-digit pruning.** Once the counts of all digits `>= k` are fixed, the
sum `S` lies in a known interval:

- `lo = t`, where the remaining slots are all zeros;
- `hi = t + z + rf·(k-1)^(k-1)`, where the remaining slots are all `k-1`.

Here `t` is the partial sum, `z` the number of zeros already known, and `rf` the
number of free slots. All numbers in `[lo, hi]` share some leading base-`b`
digits, and the final number must contain those digits. A leading digit `x >= k`
can't appear more often than `c_x`, so violating that prunes the branch. This is
the "fixed leading digits" idea from narcissistic-number searches.

**Forced digits.** A leading digit `x < k` hasn't been counted yet, but it now
must appear at least that many times. Its weight is added to `t` immediately.
That narrows `[lo, hi]` and can expose more leading digits, so this repeats until
nothing changes. The interval only shrinks on the way down, so the
leading-digit histogram is carried along and only newly exposed digits are
examined.

**Both conventions at once.** `0^0 = 0` and `0^0 = 1` differ only in what each
zero adds to the sum, which is at most `d`. The interval above is the union over
both conventions, so the whole tree is shared. The conventions are told apart
only at the leaves, where every candidate is checked exactly.

**Digit-vector arithmetic.** Numbers are stored as one byte per base-`b` digit in
AVX2 registers: one register up to base 30, two up to base 62. No bignum library
is needed. Addition is a lane-wise add followed by carry resolution with the
carry-lookahead identity `carry_in = ((generate << 1) + propagate) ^ propagate`
on 64-bit masks. Finding the shared leading digits of `lo` and `hi` is then one
vector compare and one `lzcnt`.

**Parallelism.** The tree is cut into a few tens of thousands of subtrees, which
are spread across cores with rayon's work stealing. The same cut defines the
resumable units.

The search tree grows about 2× per base, versus about 4× per base for searches
that enumerate every digit combination. Most of the work is at `d = b-1`.
