/-!
# Depth-first search with sound pruning

An abstract search tree with levels. A node at level `k` above `bottom` has a list of
candidate children; a pruning function turns each candidate into a child at level `k - 1`, or
drops it (`none`). A node at level `bottom` or below is a leaf and outputs a list.

* `dfs_sound`: every output satisfies `Q` if every leaf output does. Pruning plays no part.
* `dfs_complete`: an output `a` is found if some invariant `Inv` holds at the start, survives
  in at least one child of each inner node, and puts `a` into the output of each leaf. For the
  exact search, `Inv k N` says that a fixed solution is a completion of `N`, and each pruning
  rule is shown to keep such a child.

The recursion is on the level, so `dfs` terminates. The file uses only the Lean core.
-/

namespace Munchausen

namespace ExactSearch

universe u v x

variable {ν : Type u} {γ : Type v} {α : Type x}

/-- Depth-first search over levels: below level `bottom + 1` a node is a leaf, above it the
search descends into the children that survive pruning. `cands k N` lists the candidate children
of `N`, and `expand k N c` builds the child for candidate `c`, or prunes it (`none`). -/
def dfs (cands : Nat → ν → List γ) (expand : Nat → ν → γ → Option ν) (leaf : ν → List α)
    (bottom : Nat) : Nat → ν → List α
  | 0, N => leaf N
  | k + 1, N =>
    if k + 1 ≤ bottom then leaf N
    else ((cands (k + 1) N).filterMap (expand (k + 1) N)).flatMap (dfs cands expand leaf bottom k)

variable {cands : Nat → ν → List γ} {expand : Nat → ν → γ → Option ν} {leaf : ν → List α}
  {bottom : Nat}

/-- **Soundness.** Every output of the search is an output of some leaf. -/
theorem dfs_sound {Q : α → Prop} (hleaf : ∀ N, ∀ a ∈ leaf N, Q a) :
    ∀ k N, ∀ a ∈ dfs cands expand leaf bottom k N, Q a
  | 0, N, a, ha => hleaf N a ha
  | k + 1, N, a, ha => by
    simp only [dfs] at ha
    by_cases hk : k + 1 ≤ bottom
    · simp only [hk, ↓reduceIte] at ha
      exact hleaf N a ha
    · simp only [hk, ↓reduceIte] at ha
      obtain ⟨N', -, hN'⟩ := List.mem_flatMap.1 ha
      exact dfs_sound hleaf k N' a hN'

/-- **Completeness with sound pruning.** Let `Inv` hold at a node. Suppose that at every inner
node with `Inv`, some candidate is kept by `expand` and its child has `Inv` again (each pruning
rule spares it), and that every leaf with `Inv` outputs `a`. Then the search outputs `a`. -/
theorem dfs_complete (Inv : Nat → ν → Prop) (a : α)
    (hstep : ∀ k N, bottom < k → Inv k N →
      ∃ c ∈ cands k N, ∃ N', expand k N c = some N' ∧ Inv (k - 1) N')
    (hleaf : ∀ k N, k ≤ bottom → Inv k N → a ∈ leaf N) :
    ∀ k N, Inv k N → a ∈ dfs cands expand leaf bottom k N
  | 0, N, h => hleaf 0 N (Nat.zero_le _) h
  | k + 1, N, h => by
    simp only [dfs]
    by_cases hk : k + 1 ≤ bottom
    · simp only [hk, ↓reduceIte]
      exact hleaf _ N hk h
    · simp only [hk, ↓reduceIte]
      obtain ⟨c, hc, N', he, hN'⟩ := hstep (k + 1) N (by omega) h
      exact List.mem_flatMap.2 ⟨N', List.mem_filterMap.2 ⟨c, hc, he⟩,
        dfs_complete Inv a hstep hleaf k N' hN'⟩

end ExactSearch

end Munchausen
