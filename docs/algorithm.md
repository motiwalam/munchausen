# The search algorithm

This document explains how the search finds every Munchausen number in a base.
It covers the math that bounds the search, the optimizations in the Python
code in `src/`, and the algorithm in the Rust code in `fast/`.
`docs/comparison.md` measures each approach.

## Notation

- `b` is the base and `d` is the number of digits.
- `w(x) = x^x` is the weight of digit `x`. `w(0)` is 0 or 1, depending on
  the convention for `0^0`.
- `F(n)` is the sum of `w(x)` over the base-`b` digits `x` of `n`. A Munchausen
  number satisfies `F(n) = n`.
- `c_x` is the number of times digit `x` appears.

## How large a Munchausen number can be

A number with `d` digits is at least `b^(d-1)`. Its Munchausen sum is at most
`d * (b-1)^(b-1)`, because no digit weighs more than `(b-1)^(b-1)`.

For `d = b+1`, the sum is at most `(b+1) * (b-1)^(b-1)`. This is less than
`b^b` for every `b >= 2`, so no `(b+1)`-digit number can equal its own sum.
The gap only grows for larger `d`. So a Munchausen number has at most `b`
digits, and it is at most `b * (b-1)^(b-1)`.

Van Berkel (2009) proved the weaker bound `2 * b^b`. Kures (2021) proved that
a solution has at most `b` digits, the same result as above.

## Search over digit multisets

`F(n)` depends only on how many times each digit appears, not on their order.
So the search does not visit numbers. For each `d` from 2 to `b`, it visits
digit counts `(c_0, ..., c_{b-1})` with `c_0 + ... + c_{b-1} = d`. For each
count vector it computes the sum `S = c_0 w(0) + ... + c_{b-1} w(b-1)`. Then it
checks two things:

1. `S` has exactly `d` digits.
2. The digit counts of `S` are the same as the count vector.

There are `C(b+d-1, d)` count vectors with `d` digits. Over all `d` this is
about `4^b / sqrt(pi * b)`, so the number of count vectors grows about 4x per
base. Every search below shrinks this set.

One-digit numbers are a special case. `x^x = x` only for `x = 1`, and for
`x = 0` when `0^0 = 0`. Every search hard-codes them.

## The Python search (`src/munchausen.py`)

The Python code enumerates count vectors as sorted digit combinations with
`itertools.combinations_with_replacement`. It removes three groups of
combinations before it generates them.

### Large digits

A digit `x` with `x^x >= b^d` cannot appear in a `d`-digit Munchausen number.
The sum would already have `d+1` digits. `mx = fm(b^d)` is the first digit
that is too large, and the combinations only use digits below `mx`.

### A required number of copies

A `d`-digit number is at least `b^(d-1)`. `t = fm(b^(d-1) / d)` is the
smallest digit with `d * t^t >= b^(d-1)`. If every digit were below `t`, the
sum would be less than `b^(d-1)`. So at least one digit is `t` or larger.

For each `r` from `t` to `mx - 1`, `gcwr` then assumes that `r` appears at
least `n = ceil(b^(d-1) / r^r)` times. It prepends `n` copies of `r` and
enumerates the remaining `d - n` digits freely.

I do not know a proof for this rule. A sum can reach `b^(d-1)` through one
copy each of several large digits, and then no single digit has `n` copies.
I checked every number in bases 2 to 38 against the rule. All of them
satisfy it, except `10` in base 2. So far the rule has not removed a
solution. The rule also generates some combinations twice, once for each
qualifying `r`.

### `testbd0`

For each `r`, `testbd0` takes the smallest possible sum, `n * r^r`. It rounds
this sum up, digit by digit, to a number whose digits are all below `mx`. If
that number has more than `d` digits, the code skips the whole group for
`r`.

In base 2, `n` is 0. Then `testbd0` rejects every group, so the Python code
does not find `10` in base 2 (that is, 2 with `0^0 = 1`).

### Parallelism

`pathos` runs one process per value of `d`. The work is very uneven. In bases
16 to 28, `d = b-1` holds 55% of the combinations and `d = b` holds 26%. The
processes for small `d` finish early and wait.

## The prefix-pruned count search (`fast/src/search.rs`)

The Rust search also enumerates count vectors, but it builds them one digit at
a time. It fixes `c_{b-1}` first, then `c_{b-2}`, and so on down to `c_1`.
After each step it checks whether any completion can still work. Most partial
count vectors fail this check early, so most of the tree is never built.

### The state of a node

A node of the search tree fixes the counts of all digits from `k` to `b-1`. It
stores:

- `t`, the sum of the weights of every nonzero digit counted so far,
- `rf`, the number of digit positions that are still free,
- the digits already known to be at the front of `S` (the known prefix) and
  their counts.

The root for `d` digits has `t = 0`, `rf = d`, and an empty known prefix. It
starts at the largest digit `k` with `k^k < b^d`.

### The interval

The free positions all hold digits below `k`. If they are all 0, the sum is
smallest. If they are all `k-1`, the sum is largest. So the final sum `S`
satisfies

    lo = t    <=    S    <=    hi = t + z + rf * (k-1)^(k-1)

where `z` is the number of zeros in the known prefix (see "Both conventions in
one pass" below). The search clips the interval to `[b^(d-1), b^d - 1]`, the
`d`-digit numbers. If nothing is left, the node fails.

### The leading-digit test

All numbers in `[lo, hi]` start with the same digits, up to the first position
where `lo` and `hi` differ. `S` lies in the interval, so `S` starts with those
digits too, and they must be in the multiset. Each new leading digit `x` must
pass one test:

- If `x >= k`, its count is fixed. If the prefix holds more than `c_x`
  copies of `x`, the node fails.
- If `x < k`, its count is still open. The digit takes one free position, so
  `rf` drops by one. If `rf` is already 0, the node fails.

The same idea appears in fast searches for narcissistic numbers, where it is
called "fixed leading digits".

### Forced digits

A leading digit `x < k` must be in the multiset, even though `c_x` is not
fixed yet. The search counts it as placed: it adds `w(x)` to `t` right away.
Later, when the search reaches digit `x`, `c_x` starts at the number of copies
already placed.

This narrows the interval. `lo` grows by `w(x)`, and `hi` shrinks. The bound
for `hi` counted one more free position at `(k-1)^(k-1)`, and that position
now holds `x`. A narrower interval can
expose more leading digits, and those can force more digits. The search
repeats the test until no new digits appear.

After the leading digits, the search looks at the first unknown digit. It
lies between the digits of `lo` and `hi` at that position. If all of these
values are at least `k`, their counts are already fixed. If each of them
already has all its copies in the prefix, no number in the interval fits, and
the search drops the node. Knuth's `back-pdi.w` uses the same test. It removes
about 7% of the nodes in bases 20 to 32.

The interval only shrinks on the way down the tree. So a child keeps every
leading digit of its parent, and the search only inspects positions that are
new. The prefix and its digit counts travel with the node.

### Choosing the next count

At a node for digit `k`, the search tries `c_k = p + e` for `e = 0, 1, ..., rf`.
Here `p` is the number of copies of `k` already in the known prefix. Each value
of `e` adds `e * w(k)` to `t` and uses `e` free positions. The search builds
the interval for each child and runs the leading-digit test on it. Children
that pass become new nodes.

### Leaves

At `k = 1` every digit from 2 up has a fixed count. The free positions hold
ones and zeros. The leaf tries every number `e` of extra ones. For each `e`
and each convention, it computes the exact sum. Then it compares all `d`
digit counts of the sum with the count vector.

### Both conventions in one pass

The conventions differ only in what a zero adds to the sum: 0 or 1. The
interval above is wide enough for both:

- `lo = t` is the smallest sum under `0^0 = 0`.
- `hi = t + z + rf * (k-1)^(k-1)` adds 1 for each known zero, which covers
  `0^0 = 1`.

The extra width is at most `d`, which is tiny next to `(k-1)^(k-1)` except at
the bottom of the tree. So one tree serves both conventions. The leaves check
each convention exactly. A combined run visits 19,362,129 nodes for base 28,
and a run for one convention visited 19,361,945.

### Example: 3435 in base 10

This is the path to `3435` in the search for `d = 4`. The largest usable digit
is 5, because `5^5 = 3125 < 10^4 <= 6^6`.

1. Digit 5, one copy. `t = 3125`, `rf = 3`, `hi = 3125 + 3 * 4^4 = 3893`. The
   interval `[3125, 3893]` has the leading digit 3. Digit 3 is below 5, so it
   is forced. `t = 3152`, `rf = 2`, `hi = 3152 + 2 * 256 = 3664`. Nothing new
   appears.
2. Digit 4, one copy. `t = 3408`, `rf = 1`, `hi = 3408 + 3^3 = 3435`. The
   interval `[3408, 3435]` has the leading digits 34. The new 4 is within the
   one copy of 4.
3. Digit 3, one more copy beyond the forced one. `t = 3435`, `rf = 0`, and
   `lo = hi = 3435`. The new digits 3 and 5 are within the counts: two 3s, one
   5.
4. Digits 2 and 1 get no copies. The leaf finds `S = 3435` with digits
   {3, 3, 4, 5}, which is the count vector. `3435` has no zeros, so it is a
   solution under both conventions.

Two siblings in step 1 show how branches fail:

- No copies of 5: `[0, 4 * 256] = [0, 1024]` clips to `[1000, 1024]`, which
  starts with 10. Digit 1 and digit 0 are forced. Then `hi = 1 + 1 + 2 * 256 =
  514` is below 1000, and the node fails.
- Two copies of 5: `t = 6250`, and `[6250, 6762]` starts with 6. Digit 6 is
  above 5, and its count is 0, so the node fails.

### Why the search misses nothing

Each rule only removes count vectors that cannot be solutions.

- The interval holds every sum that a completion of the node can reach.
- Every leading digit of the interval is a digit of every reachable sum. A
  solution must contain it.
- Forcing a digit only removes completions that leave it out.
- The first unknown digit of every reachable sum lies in the range that the
  test checks. If no value in that range has a copy left, no completion fits.

A count vector reaches a leaf only if it passed every check on the way down.
The leaf then compares the exact sum with the vector.

## Implementation

### Digit vectors

The search never converts between binary and base `b`. It stores each number
as one byte per base-`b` digit, with the least significant digit first, in
AVX2 registers. One 32-byte register holds 32 digits and covers numbers with
up to 30 digits. Two registers cover up to 62 digits. Two lanes stay free for
carries out of the top digit. A lane holds at most `2b - 1` before the carry
step, so bases up to 127 fit in a byte. No bignum library is needed, and the code is the same for every
base.

Addition adds the lanes, then resolves carries with a carry-lookahead identity
on 64-bit masks:

    generate  = lanes whose sum is at least b
    propagate = lanes whose sum is exactly b-1
    carry_in  = ((generate << 1) + propagate) ^ propagate

The integer addition moves each carry through a run of propagating lanes in one
step. The code then adds `carry_in` and subtracts `b` from every lane that
reached `b`. One addition takes about 15 vector and scalar instructions.

The leading digits shared by `lo` and `hi` come from one lane-wise compare. A
movemask turns it into a bitmask, and `lzcnt` gives the first differing
position. The digits themselves are bytes, so the search reads them directly.

### Incremental updates

When `e` grows by one, `t` grows by `w(k)` and `hi` grows by
`w(k) - w(k-1)`. The search keeps both as running sums, so each step costs two
additions. A table holds `m * w(x)` for every digit `x` and every `m <= d`.
The search uses it to rebuild `hi` after a forced digit.

### Parallelism and resumable runs

The search expands every root four levels deep, in a fixed order. This gives
33,801 subtrees for base 28 and 113,884 for base 35. Rayon spreads the subtrees
over the cores with work stealing. Each subtree splits again, four levels
below its root, into parallel tasks.

The fixed order makes the subtree list the same in every run. With
`--journal`, the program appends one line to the journal file when a subtree
finishes. It appends another line for each solution, at the moment it finds
it. After an interruption, the same command skips every subtree that the
journal marks as done.

### Checks

Before the program prints a number, it recomputes the Munchausen sum with
arbitrary-precision integers (`num-bigint`). `cargo test` compares the search
with the brute force (bases 2 to 9) and the reference search (bases 10 to 22),
for both vector widths. The reference search is a plain `u128` version of the
leading-digit test.

### Limits

Each extra base costs about 1.9x more time. Base 38 took 520 seconds on the
test laptop. At that rate, base 40 takes about 30 minutes and base 45 about
13 hours. Numbers with more than 62 digits need wider digit vectors. Bases
from 63 to 127 work with `--max-digits 62` or less.
