import AFTD.Prelude

/-!
# merge_adjacent_blocks

Topic: combinatorics   Node: 19bcfb6a3ae5

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 1

For a type α with [DecidableEq α], a list of finite sets l : List (Finset α), and an index t : ℕ, merge_adjacent_blocks l t replaces the blocks at indices t and t + 1 with their union l[t] ∪ l[t + 1], returning the list l unmodified if t + 1 ≥ l.length or if l has fewer than two elements.
-/

/-- Merging adjacent blocks at index t in a list of blocks, returning the list unchanged if out of bounds. -/
def merge_adjacent_blocks {α : Type*} [DecidableEq α] : List (Finset α) → ℕ → List (Finset α)
| b₁ :: b₂ :: rest, 0 => (b₁ ∪ b₂) :: rest
| b :: rest, t + 1 => b :: merge_adjacent_blocks rest t
| l, _ => l
