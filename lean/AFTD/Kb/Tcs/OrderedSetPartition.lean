import AFTD.Prelude

/-!
# OrderedSetPartition

Topic: combinatorics   Node: 5fb392f73930

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 1

For a finite type α equipped with [DecidableEq α] and [Fintype α], an ordered set partition of α is a structure with fields: blocks, a list of finite subsets of α (List (Finset α)); nonempty_blocks, asserting that each block B in blocks is nonempty (B.Nonempty); pairwise_disjoint, asserting that blocks is pairwise disjoint (blocks.Pairwise Disjoint); and union_eq, asserting that the union of the blocks in blocks (blocks.toFinset.biUnion id) equals the universal set Finset.univ.
-/

/-- An ordered set partition of a finite type is a list of non-empty, pairwise disjoint blocks whose union is the universal set. -/
structure OrderedSetPartition (α : Type*) [DecidableEq α] [Fintype α] where
  blocks : List (Finset α)
  nonempty_blocks : ∀ B ∈ blocks, B.Nonempty
  pairwise_disjoint : blocks.Pairwise Disjoint
  union_eq : blocks.toFinset.biUnion id = Finset.univ
