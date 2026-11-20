import AFTD.Prelude

/-!
# BinTree

Topic: graphs   Node: b48409ab0bd8

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The inductive type BinTree of ordered full binary trees with constructors leaf and node left right.
-/

/-- Ordered full binary trees: each tree is either a leaf or an internal node with left and right subtrees. -/
inductive BinTree | leaf : BinTree
  | node (left right : BinTree) : BinTree
  deriving DecidableEq
