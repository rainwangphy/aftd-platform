import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.PlaneTreeNumLeaves
import AFTD.Kb.Tcs.IsMLeafy
import AFTD.Kb.Tcs.PlaneTreeNumInternal

/-!
# in_m_leafy_trees

Topic: combinatorics   Node: 154cf17dc9e7

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.2

LT_n^m is the set of m-leafy trees with n internal vertices and mn + 1 leaves.
-/

/-- Membership in LT_n^m: m-leafy trees with n internal vertices and mn + 1 leaves. -/
def in_m_leafy_trees (m n : ℕ) (t : PlaneTree) : Prop := is_m_leafy m t ∧ plane_tree_num_internal t = n ∧ plane_tree_num_leaves t = m * n + 1
