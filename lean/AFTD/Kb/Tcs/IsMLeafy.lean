import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTreeSubtrees
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.PlaneTreeNumLeaves
import AFTD.Kb.Tcs.PlaneTreeNumInternal

/-!
# is_m_leafy

Topic: combinatorics   Node: 74fa4203edac

Provenance: formalization of a published result. Source: arXiv:2611.10154 Def. 2.2

A tree T is m-leafy if every rooted subtree T_v satisfies ℓ(T_v) > m * n(T_v).
-/

/-- Predicate that a plane tree is m-leafy. -/
def is_m_leafy (m : ℕ) (t : PlaneTree) : Prop := ∀ s ∈ plane_tree_subtrees t, m * plane_tree_num_internal s < plane_tree_num_leaves s
