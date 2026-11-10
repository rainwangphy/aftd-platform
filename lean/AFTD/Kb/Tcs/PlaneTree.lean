import AFTD.Prelude

/-!
# PlaneTree

Topic: combinatorics   Node: 5992628e35be

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.2

A finite plane tree is either a leaf or an internal node with a list of child plane trees.
-/

/-- Inductive type of finite plane trees with ordered children. -/
inductive PlaneTree : Type | leaf : PlaneTree | node (children : List PlaneTree) : PlaneTree
