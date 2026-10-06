import AFTD.Prelude

/-!
# binary_tree_num_leaves_le_pow_height

Topic: algorithms   Node: 175ebf8a32f3

Provenance: formalization of a published result. Source: standard textbook result (data structures: a binary tree of height h has at most 2^h leaves)

The number of leaves of any binary tree is at most 2 raised to its height.
-/

/-- Every binary tree of height h has at most 2^h leaves. -/
theorem binary_tree_num_leaves_le_pow_height {α : Type*} (t : BinaryTree α) :
    t.numLeaves ≤ 2 ^ t.height := by
  induction t with
  | nil => simp
  | node _ a b ha hb =>
    simp only [BinaryTree.numLeaves, BinaryTree.height]
    have h1 : 2 ^ a.height ≤ 2 ^ max a.height b.height :=
      Nat.pow_le_pow_right (by omega) (le_max_left a.height b.height)
    have h2 : 2 ^ b.height ≤ 2 ^ max a.height b.height :=
      Nat.pow_le_pow_right (by omega) (le_max_right a.height b.height)
    omega
