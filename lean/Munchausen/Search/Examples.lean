import Munchausen.Search.Correctness

/-!
# The exact search on small bases

* `#guard` runs the search (compiled code, outside any proof) and compares it with the lines of
  `output/b2-41-0.txt` and `output/b2-41-1.txt`, written by the Rust code, for bases 2 to 12.
* `#guard` compares the node counts of the tree with those of `fast search 2 14 --unit-depth 0`
  (stderr), for the residue rule alone, the default last-digit tests, one convention, and other
  digit counts. They agree in every base from 2 to 12, so the Lean tree is the Rust tree.
* The theorems `solutions_two` to `solutions_seven` are checked by the kernel with `decide`. With
  `found_eq_solutions` they give the complete list of solutions in these bases, as theorems.
-/

set_option linter.hashCommand false

namespace Munchausen

namespace ExactSearch

/-- The solutions in base `b` under `0^0 = m` in the form of the Rust output: sorted digit
strings, leading digit first. The Rust code writes 0 as the string `(0)`, a solution under
`0^0 = 0`; the verified search leaves 0 out (see `Spec.lean`), so it is added here. -/
def rustLine (b m : ℕ) : List (List ℕ) :=
  (if m = 0 then [[0]] else []) ++
    ((found b [0, 1] m).sort (· ≤ ·)).map fun n => (Nat.digits b n).reverse

/-! ### The Rust output for bases 2 to 12 -/

#guard rustLine 2 0 = [[0], [1]]
#guard rustLine 3 0 = [[0], [1], [1, 2], [2, 2]]
#guard rustLine 4 0 = [[0], [1], [1, 3, 0], [1, 3, 1], [3, 1, 3]]
#guard rustLine 5 0 = [[0], [1], [1, 0, 3], [2, 0, 2, 4]]
#guard rustLine 6 0 = [[0], [1], [2, 2, 3, 5, 2], [2, 3, 4, 5, 2]]
#guard rustLine 7 0 = [[0], [1], [1, 3, 4, 5, 4]]
#guard rustLine 8 0 = [[0], [1], [4, 0, 0], [4, 0, 1]]
#guard rustLine 9 0 = [[0], [1], [3, 0], [3, 1], [1, 5, 6, 2, 6, 2], [1, 6, 4, 7, 0, 6, 3],
  [1, 6, 5, 6, 5, 4, 7], [3, 4, 6, 6, 4, 0, 8, 4]]
#guard rustLine 10 0 = [[0], [1], [3, 4, 3, 5], [4, 3, 8, 5, 7, 9, 0, 8, 8]]
#guard rustLine 11 0 = [[0], [1], [6, 6, 5, 0, 0], [6, 6, 5, 0, 1], [5, 1, 7, 5, 0, 3],
  [1, 8, 4, 5, 3, 2, 7, 8], [1, 8, 4, 5, 3, 4, 8, 7]]
#guard rustLine 12 0 = [[0], [1], [3, 10, 6, 7, 10, 5, 4, 8, 3, 2]]

#guard rustLine 2 1 = [[1], [1, 0]]
#guard rustLine 3 1 = [[1], [1, 2], [2, 2]]
#guard rustLine 4 1 = [[1], [1, 3, 1], [3, 1, 3]]
#guard rustLine 5 1 = [[1]]
#guard rustLine 6 1 = [[1], [2, 2, 3, 5, 2], [2, 3, 4, 5, 2]]
#guard rustLine 7 1 = [[1], [1, 3, 4, 5, 4]]
#guard rustLine 8 1 = [[1]]
#guard rustLine 9 1 = [[1], [3, 1], [1, 5, 6, 2, 6, 2], [1, 6, 5, 6, 5, 4, 7]]
#guard rustLine 10 1 = [[1], [3, 4, 3, 5]]
#guard rustLine 11 1 = [[1], [1, 8, 4, 5, 3, 2, 7, 8], [1, 8, 4, 5, 3, 4, 8, 7]]
#guard rustLine 12 1 = [[1], [3, 10, 6, 7, 10, 5, 4, 8, 3, 2]]

-- The residue rule for one convention (`-m 0` or `-m 1`) prunes more, and keeps the
-- solutions of that convention.
#guard (List.range' 2 11).all fun b =>
  found b [0] 0 = found b [0, 1] 0 && found b [1] 1 = found b [0, 1] 1

-- The last-digit tests keep every solution, with any numbers of tested digits.
#guard (List.range' 2 9).all fun b => [(0, 0), (1, 0), (2, 1), (5, 4)].all fun (l, p) =>
  foundWith b [0, 1] l p 0 = found b [0, 1] 0 && foundWith b [0, 1] l p 1 = found b [0, 1] 1

/-! ### Node counts against the Rust code -/

/-- The nodes of the tree below `N`: every node that survives its tests, leaves included. This
is what `fast search` counts. -/
def dfsNodes {ν γ : Type} (cands : ℕ → ν → List γ) (expand : ℕ → ν → γ → Option ν)
    (bottom : ℕ) : ℕ → ν → ℕ
  | 0, _ => 1
  | k + 1, N =>
    if k + 1 ≤ bottom then 1
    else 1 + (((cands (k + 1) N).filterMap (expand (k + 1) N)).map
      (dfsNodes cands expand bottom k)).sum

/-- The nodes of the search in base `b`, over the lengths 2 to `b`. -/
def searchNodes (b : ℕ) (ms : List ℕ) (low pair : ℕ) : ℕ :=
  ((List.range' 2 (maxLen b - 1)).map fun d =>
    let P : Params := ⟨b, d, ms, low, pair⟩
    dfsNodes (childCands P) (expandChild P) 2 (kmax b d + 1) root).sum

/-- The node counts of `fast search 2 12 --unit-depth 0 -j 1` with the given options. Without
`--unit-depth 0` the Rust code builds its work units without the last-digit tests. -/
def rustNodes (ms : List ℕ) (low pair : ℕ) : List ℕ :=
  match ms, low, pair with
  | [0, 1], 0, 0 => [1, 4, 8, 11, 19, 30, 59, 126, 195, 373, 510]
  | [0, 1], 3, 2 => [1, 4, 8, 9, 13, 18, 31, 78, 116, 203, 302]
  | [0], 3, 2 => [1, 4, 7, 9, 13, 18, 30, 78, 108, 202, 293]
  | [1], 3, 2 => [1, 4, 8, 4, 13, 18, 28, 65, 109, 186, 293]
  | [0, 1], 1, 0 => [1, 4, 8, 10, 16, 27, 44, 102, 178, 320, 447]
  | [0, 1], 2, 1 => [1, 4, 8, 10, 14, 23, 38, 89, 147, 254, 369]
  | _, _, _ => []

#guard [([0, 1], 0, 0), ([0, 1], 3, 2), ([0], 3, 2), ([1], 3, 2), ([0, 1], 1, 0),
    ([0, 1], 2, 1)].all fun (ms, l, p) =>
  (List.range' 2 11).map (fun b => searchNodes b ms l p) == rustNodes ms l p

/-! ### Complete lists of solutions, checked by the kernel -/

/-- The positive solutions in base 2: `1`, and `2 = (1,0)` under `0^0 = 1`. -/
theorem solutions_two : solutions 2 0 = {1} ∧ solutions 2 1 = {1, 2} := by
  rw [← found_eq_solutions (ms := [0, 1]) le_rfl (by norm_num) (by simp),
    ← found_eq_solutions (ms := [0, 1]) le_rfl le_rfl (by simp)]
  decide

/-- Base 3: `5 = (1,2)` and `8 = (2,2)`. -/
theorem solutions_three : solutions 3 0 = {1, 5, 8} ∧ solutions 3 1 = {1, 5, 8} := by
  rw [← found_eq_solutions (ms := [0, 1]) (by norm_num) (by norm_num) (by simp),
    ← found_eq_solutions (ms := [0, 1]) (by norm_num) le_rfl (by simp)]
  decide

/-- Base 4: `28 = (1,3,0)`, `29 = (1,3,1)` and `55 = (3,1,3)`. -/
theorem solutions_four : solutions 4 0 = {1, 28, 29, 55} ∧ solutions 4 1 = {1, 29, 55} := by
  rw [← found_eq_solutions (ms := [0, 1]) (by norm_num) (by norm_num) (by simp),
    ← found_eq_solutions (ms := [0, 1]) (by norm_num) le_rfl (by simp)]
  decide

/-- Base 5: `28 = (1,0,3)` and `264 = (2,0,2,4)`, both under `0^0 = 0` only. -/
theorem solutions_five : solutions 5 0 = {1, 28, 264} ∧ solutions 5 1 = {1} := by
  rw [← found_eq_solutions (ms := [0, 1]) (by norm_num) (by norm_num) (by simp),
    ← found_eq_solutions (ms := [0, 1]) (by norm_num) le_rfl (by simp)]
  decide

/-- Base 6: `3164 = (2,2,3,5,2)` and `3416 = (2,3,4,5,2)`. -/
theorem solutions_six : solutions 6 0 = {1, 3164, 3416} ∧ solutions 6 1 = {1, 3164, 3416} := by
  rw [← found_eq_solutions (ms := [0, 1]) (by norm_num) (by norm_num) (by simp),
    ← found_eq_solutions (ms := [0, 1]) (by norm_num) le_rfl (by simp)]
  decide

/-- Base 7: `3665 = (1,3,4,5,4)`. -/
theorem solutions_seven : solutions 7 0 = {1, 3665} ∧ solutions 7 1 = {1, 3665} := by
  rw [← found_eq_solutions (ms := [0, 1]) (by norm_num) (by norm_num) (by simp),
    ← found_eq_solutions (ms := [0, 1]) (by norm_num) le_rfl (by simp)]
  decide

end ExactSearch

end Munchausen
