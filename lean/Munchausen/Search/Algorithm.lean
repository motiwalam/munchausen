import Munchausen.Search.Spec
import Munchausen.Search.Dfs

/-!
# The exact search: a functional implementation

This is the exact search of `fast/src/search.rs` (`docs/algorithm.md`, "The prefix-pruned
count search"), written for reading rather than speed. It is executable: `Examples.lean` runs it
on small bases. `Correctness.lean` proves that it returns exactly the solutions.

The search fixes a length `d` and enumerates count vectors `(c_0, ..., c_{b-1})` with
`∑ c_x = d`, deciding `c_x` from the largest digit down. A node at level `k` has decided the
counts of the digits `x ≥ k`; its `rf` free slots hold digits below `k`. Every completion of the
node has its sum `S` in an interval `[lo, hi]`. The common leading digits of `lo` and `hi` are
leading digits of `S`, so they must be in the multiset: a digit `x ≥ k` must fit in `c_x`, and a
digit below `k` is forced into a free slot. The search repeats this until nothing new appears
(`settle`). A few more tests prune nodes; the leaves check each candidate exactly.

## What differs from the Rust code

The tree, the tests and their order are the same. The representation is simpler:

* A node stores only the counts `cnt` and the length `pl` of its known prefix. The Rust node
  keeps `t`, `hi`, `rf` and the residues as running sums; here they are recomputed from `cnt`
  (`t`, `hi`, `rf`, `residue`). The Rust code reads the known prefix from the lanes of `lo`;
  here it is `topDigits b d (clo ..) pl`.
* `cnt x` holds the decided count `c_x` for `x ≥ k`, and the number of forced copies of `x` for
  `x < k`. The Rust code keeps the first in `cnt: Hist` and counts the second in the prefix
  lanes on demand (`occk` in `Cursor::new`).
* The free slots are bounded by `w 1 (k-1) = (k-1)^(k-1)`, the Rust `wmax[k-1]` for the weights
  `x^x`, and a forced zero counts as 1 in `hi` (the Rust `w_hi[0]`), so one tree serves both
  conventions.
* Numbers are natural numbers, not digit vectors. Nothing overflows.
* `settle` takes a fuel argument `d + 1` for its loop. Each round with forced digits extends the
  prefix, so the loop stops within `d` rounds. Running out of fuel would keep the node, which is
  always safe.
* The leaf checks only the conventions in `ms`. The Rust leaf checks both and `main.rs` prints
  the ones asked for; the output is the same.
* The number 0 is not output (see `Spec.lean`).
-/

namespace Munchausen

namespace ExactSearch

open Finset

/-- The parameters of the search for one length: the base `b`, the number of digits `d`, and
the conventions `0^0 = m`, `m ∈ ms`, whose solutions the search must keep. The residue rule
keeps a node if one of them passes (`prune.residue` in the Rust code, `-m` on the command
line). -/
structure Params where
  b : ℕ
  d : ℕ
  ms : List ℕ

/-- A node of the search tree (Rust: `Node` with the histogram `cnt` and the known lanes of
`lo`). At level `k`, `cnt x` is the decided count `c_x` for `x ≥ k`, and the number of forced
copies of `x` for `x < k`. `pl` is the number of known leading digits of the sum (Rust: `d - pp`).
-/
structure Node where
  cnt : ℕ → ℕ
  pl : ℕ

/-- The root of the tree for one length: nothing decided, nothing known. -/
def root : Node := ⟨fun _ => 0, 0⟩

variable (P : Params)

/-! ### The quantities of a node -/

/-- The number of placed digits: the decided ones and the forced ones. -/
def placed (N : Node) : ℕ := ∑ x ∈ range P.b, N.cnt x

/-- The number of free slots `rf` (Rust: `Node::rf`). They hold digits below the level. -/
def rf (N : Node) : ℕ := P.d - placed P N

/-- The weight `t` of the placed digits under `0^0 = 0` (Rust: `Node::t`). Every completion has
a sum of at least `t`. -/
def t (N : Node) : ℕ := ∑ x ∈ range P.b, N.cnt x * w 0 x

/-- The upper end `hi` of the interval at level `k` (Rust: `Node::hi`, in the form
`t + z + rf W(k-1)`, Lemma 31.4). A placed zero counts as 1, and a free slot as the largest
weight below `k`, `(k-1)^(k-1)`. -/
def hi (k : ℕ) (N : Node) : ℕ := ∑ x ∈ range P.b, N.cnt x * w 1 x + rf P N * w 1 (k - 1)

/-- `lo` clipped to the `d`-digit numbers (Rust: `Params::clip_lo`). -/
def clo (N : Node) : ℕ := max (t P N) (P.b ^ (P.d - 1))

/-- `hi` clipped to the `d`-digit numbers. -/
def chi (k : ℕ) (N : Node) : ℕ := min (hi P k N) (P.b ^ P.d - 1)

/-- The number of common leading digits of two `d`-digit numbers (Rust: the `eq_mask` and
`leading_zeros` at the top of `settle`). -/
def prefixLen (lo hi : ℕ) : ℕ :=
  Nat.findGreatest (fun l => lo / P.b ^ (P.d - l) = hi / P.b ^ (P.d - l)) P.d

/-- The residue of the placed digits under `0^0 = m`: `∑ cnt_x (w(x) - x)`, to be read modulo
`b - 1` (Rust: `Node::res`, section 31.2.1). -/
def residue (m : ℕ) (N : Node) : ℕ := ∑ x ∈ range P.b, N.cnt x * g m x

/-! ### The tests -/

/-- **The residue test** (Theorem 31.1, Rust: `Params::res_ok`). For a node with one free slot
at level `k`: some convention `m ∈ ms` and some digit `y < k` in the slot give
`∑ c_x (w(x) - x) ≡ 0 (mod b - 1)`. -/
def resOk (k : ℕ) (N : Node) : Bool :=
  P.ms.any fun m => (List.range k).any fun y => (residue P m N + g m y) % (P.b - 1) == 0

/-- A node at level `k` fails the residue test: it has one free slot and no completion passes
the congruence. -/
def residueFails (k : ℕ) (N : Node) : Bool := rf P N == 1 && !resOk P k N

/-- **The first unknown digit** (Rust: `first_digit_ok`). Let the digit of `lo` just after the
known prefix be `x0 ≥ k`. That digit of the sum lies between the digits `x0` and `x1` of `lo`
and `hi`, and its count is decided. Some value in `[x0, x1]` must have a copy left. -/
def firstDigitOk (k : ℕ) (N : Node) : Bool :=
  if P.d ≤ N.pl then true
  else
    let lo := clo P N
    let x0 := topDigit P.b P.d lo N.pl
    if x0 < k then true
    else
      let x1 := topDigit P.b P.d (chi P k N) N.pl
      (List.range' x0 (x1 + 1 - x0)).any fun x => (topDigits P.b P.d lo N.pl).count x < N.cnt x

/-- **Forced digits, iterated to a fixed point** (Rust: `Search::settle`). One round reads the
common leading digits of `[clo, chi]` beyond the known prefix. A new digit `x ≥ k` must fit in
`c_x`: the prefix may hold at most `cnt x` copies. A new digit below `k` is forced: it takes a
free slot and its weight goes into `t`. Forcing narrows the interval, so the round repeats until
no digit is forced. `none` means the node fails. -/
def settle (k : ℕ) : ℕ → Node → Option Node
  | 0, N => some N
  | fuel + 1, N =>
    let lo := clo P N
    let L := prefixLen P lo (chi P k N)
    if L ≤ N.pl then some N
    else
      let new := (List.range (L - N.pl)).map fun i => topDigit P.b P.d lo (N.pl + i)
      let forced := new.filter (· < k)
      if rf P N < forced.length then none
      else if new.any (fun x => k ≤ x && N.cnt x < (topDigits P.b P.d lo L).count x) then none
      else
        let N' : Node := ⟨fun x => N.cnt x + forced.count x, L⟩
        if forced.isEmpty then some N'
        else if P.b ^ P.d ≤ t P N' || hi P k N' < P.b ^ (P.d - 1) then none
        else settle k fuel N'

/-- The child of `N` that decides `c_j = cnt j + e`: `e` free slots take the digit `j`, on top of
the copies of `j` already forced (Rust: `ck = occk + e` in `next_child`). -/
def childAt (j e : ℕ) (N : Node) : Node := ⟨Function.update N.cnt j (N.cnt j + e), N.pl⟩

/-- The tests on one child at level `j`, in the order of `next_child`: the residue test, the
interval test `hi ≥ b^(d-1)`, `settle`, the first unknown digit, and the residue test again
after the forced digits. The test `lo < b^d` is in `children`, as a `break`. -/
def tryChild (j : ℕ) (c : Node) : Option Node :=
  if residueFails P j c then none
  else if hi P j c < P.b ^ (P.d - 1) then none
  else
    match settle P j (P.d + 1) c with
    | none => none
    | some c' =>
      if !firstDigitOk P j c' then none
      else if residueFails P j c' then none
      else some c'

/-- The values `e` for the children of a node at level `k`: `e = 0, 1, ..., rf`, stopping at the
first child with `lo ≥ b^d`, since `lo` grows with `e` (the `break` in `next_child`). -/
def childCands (k : ℕ) (N : Node) : List ℕ :=
  (List.range (rf P N + 1)).takeWhile fun e => t P (childAt (k - 1) e N) < P.b ^ P.d

/-- The children of a node at level `k`: decide the count of the digit `k - 1`. -/
def expandChild (k : ℕ) (N : Node) (e : ℕ) : Option Node := tryChild P (k - 1) (childAt (k - 1) e N)

/-- The counts at a leaf with `e` extra ones: the free slots hold `e` ones and `r - e` zeros. -/
def leafCnt (N : Node) (r e : ℕ) : ℕ → ℕ :=
  fun x => if x = 1 then N.cnt 1 + e else if x = 0 then N.cnt 0 + (r - e) else N.cnt x

/-- The exact test at a leaf: `S` has `d` digits and its digit counts are `c`. -/
def leafCheck (c : ℕ → ℕ) (S : ℕ) : Bool :=
  decide (P.b ^ (P.d - 1) ≤ S) && decide (S < P.b ^ P.d) &&
    (List.range P.b).all fun x => (topDigits P.b P.d S P.d).count x == c x

/-- **A leaf** (Rust: `Search::leaf`). Every digit from 2 up is decided, and the free slots hold
ones and zeros. For each number `e` of extra ones and each convention `m`, compute the sum
`S = ∑ c_x w(x)` and compare the digits of `S` with the counts. -/
def leaf (N : Node) : List (ℕ × ℕ) :=
  (List.range (rf P N + 1)).flatMap fun e =>
    P.ms.filterMap fun m =>
      let c := leafCnt N (rf P N) e
      let S := ∑ x ∈ range P.b, c x * w m x
      if leafCheck P c S then some (m, S) else none

/-- **The tree for one length** (Rust: `Search::rec_seq`). Levels run down from the root to 2;
a node at level 2 is a leaf. Outputs are pairs `(m, n)`: `n` is a solution under `0^0 = m`. -/
def explore : ℕ → Node → List (ℕ × ℕ) := dfs (childCands P) (expandChild P) (leaf P) 2

/-- The largest digit that a `d`-digit solution can hold: `x^x < b^d` (Proposition 1.2, Rust:
`kmax` in `Params::new`). -/
def kmax (b d : ℕ) : ℕ := Nat.findGreatest (fun x => x ^ x < b ^ d) (b - 1)

/-- The search for the `d`-digit solutions. The root sits at level `kmax + 1`: the digits above
`kmax` have count 0. -/
def searchLen (b d : ℕ) (ms : List ℕ) : List (ℕ × ℕ) :=
  explore ⟨b, d, ms⟩ (kmax b d + 1) root

/-- The one-digit solutions, `x^x = x`, which the Rust code lists apart (`run_search_n`). -/
def oneDigit (b : ℕ) (ms : List ℕ) : List (ℕ × ℕ) :=
  ms.flatMap fun m => ((List.range b).filter fun x => 0 < x ∧ w m x = x).map fun x => (m, x)

/-- **The exact search** in base `b` for the conventions `ms`: the one-digit solutions, then the
lengths `d = 2, ..., maxLen b`. -/
def search (b : ℕ) (ms : List ℕ) : List (ℕ × ℕ) :=
  oneDigit b ms ++ (List.range' 2 (maxLen b - 1)).flatMap fun d => searchLen b d ms

/-- The solutions that the search finds under `0^0 = m`, as a `Finset`. -/
def found (b : ℕ) (ms : List ℕ) (m : ℕ) : Finset ℕ :=
  (((search b ms).filter fun p => p.1 = m).map Prod.snd).toFinset

end ExactSearch

end Munchausen
