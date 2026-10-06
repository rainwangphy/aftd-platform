import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryTreeNumLeavesLePowHeight

/-!
# comparison_sort_decision_tree_height_ge

Topic: algorithms   Node: 6d222261097f

Provenance: formalization of a published result. Source: standard textbook result (algorithms: decision-tree lower bound for comparison sorting)

If a binary decision tree has at least n! leaves, then 2^(height) >= n!, establishing the comparison sorting lower bound.
-/

/-- Any decision tree capable of distinguishing n! permutations has height at least log_2(n!). -/
theorem comparison_sort_decision_tree_height_ge {α : Type*} (t : BinaryTree α) (n : ℕ)
    (h : n.factorial ≤ t.numLeaves) :
    n.factorial ≤ 2 ^ t.height := h.trans (binary_tree_num_leaves_le_pow_height t)
