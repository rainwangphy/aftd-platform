import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryTreeLabels

/-!
# binary_tree_bounded_child_overlap

Topic: combinatorics   Node: 9e4e1179c203

Provenance: formalization of a published result. Source: arXiv:2611.04184 Section 4.2 (Short permutation pattern waves: The complete length-five classification)

For any type α with decidable equality and any natural number C, binary_tree_bounded_child_overlap C on BinaryTree α is defined recursively: it holds on nil, and on a node with left child l and right child r, it holds if and only if (binary_tree_labels l ∩ binary_tree_labels r).card ≤ C, and the property holds recursively on both l and r.
-/

/-- Predicate stating that every vertex has left-right child subtree label overlap at most C. -/
def binary_tree_bounded_child_overlap {α : Type*} [DecidableEq α] (C : ℕ) : BinaryTree α → Prop
| .nil => True
| .node _ l r => (binary_tree_labels l ∩ binary_tree_labels r).card ≤ C ∧
    binary_tree_bounded_child_overlap C l ∧ binary_tree_bounded_child_overlap C r
