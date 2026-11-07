import AFTD.Prelude

/-!
# binary_tree_labels

Topic: combinatorics   Node: e3e64db28c13

Provenance: formalization of a published result. Source: arXiv:2611.04184 Section 4.2 (Short permutation pattern waves: The complete length-five classification)

For any type α with decidable equality, and any binary tree t : BinaryTree α, the finite set binary_tree_labels t : Finset α of labels occurring in t is defined recursively: the empty tree nil has empty label set ∅, and a node with label a, left child l, and right child r has label set given by inserting a into the union of the label sets of l and r (insert a (binary_tree_labels l ∪ binary_tree_labels r)).
-/

/-- The finite set of class labels occurring in a binary tree. -/
def binary_tree_labels {α : Type*} [DecidableEq α] : BinaryTree α → Finset α
| .nil => ∅
| .node a l r => insert a (binary_tree_labels l ∪ binary_tree_labels r)
