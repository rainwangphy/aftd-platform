import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedSetPartition
import AFTD.Kb.Tcs.MergeAdjacentBlocks

/-!
# is_child_of

Topic: combinatorics   Node: db5d82ac0a5b

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 1

For a finite type α with decidable equality and ordered set partitions a and b of α, b is a child of a (is_child_of b a) if there exists an index t with t + 1 < b.blocks.length such that a.blocks is obtained by merging adjacent blocks of b.blocks at index t.
-/

/-- An element b is a child of a if a is obtained by merging two adjacent blocks of b. -/
def is_child_of {α : Type*} [DecidableEq α] [Fintype α]
    (b : OrderedSetPartition α) (a : OrderedSetPartition α) : Prop :=
  ∃ t : ℕ, t + 1 < b.blocks.length ∧ a.blocks = merge_adjacent_blocks b.blocks t
