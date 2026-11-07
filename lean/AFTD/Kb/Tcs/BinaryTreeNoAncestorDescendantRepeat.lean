import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryTreeLabels

/-!
# binary_tree_no_ancestor_descendant_repeat

Topic: combinatorics   Node: e2b78d23c611

Provenance: formalization of a published result. Source: arXiv:2611.04184 Section 4.2 (Short permutation pattern waves: The complete length-five classification)

For any type α with decidable equality, binary_tree_no_ancestor_descendant_repeat on BinaryTree α is defined recursively: it holds on nil, and on a node with label a, left subtree l, and right subtree r, it holds if and only if a ∉ binary_tree_labels l, a ∉ binary_tree_labels r, and the property holds recursively on both l and r.
-/

/-- Predicate stating that no class is repeated on an ancestor-descendant pair in a binary tree. -/
def binary_tree_no_ancestor_descendant_repeat {α : Type*} [DecidableEq α] : BinaryTree α → Prop
| .nil => True
| .node a l r => a ∉ binary_tree_labels l ∧ a ∉ binary_tree_labels r ∧
    binary_tree_no_ancestor_descendant_repeat l ∧ binary_tree_no_ancestor_descendant_repeat r
