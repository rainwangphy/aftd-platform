import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTreeSubtrees
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.Op1429MirrorSymmetricMLeafyTreesNOneUnique

/-!
# plane_tree_subtrees_node

Topic: combinatorics   Node: 8cf617fef50a

Provenance: helper lemma. step towards op_1430_leafy_tree_card

The rooted subtrees of a node with children cs are the node itself together with the rooted subtrees of each child: s is a rooted subtree of node cs iff s = node cs or s is a rooted subtree of some c ∈ cs.
-/

/-- Membership in the subtree list of a node, unfolded one level. -/
theorem plane_tree_subtrees_node (cs : List PlaneTree) (s : PlaneTree) :
    s ∈ plane_tree_subtrees (PlaneTree.node cs) ↔
      s = PlaneTree.node cs ∨ ∃ c ∈ cs, s ∈ plane_tree_subtrees c := by first | exact op_1429_mirror_symmetric_m_leafy_trees_n_one_unique | (apply op_1429_mirror_symmetric_m_leafy_trees_n_one_unique <;> assumption) | (apply op_1429_mirror_symmetric_m_leafy_trees_n_one_unique <;> simp_all) | simpa using op_1429_mirror_symmetric_m_leafy_trees_n_one_unique | (simp only [PlaneTree, plane_tree_subtrees] at *; first | exact op_1429_mirror_symmetric_m_leafy_trees_n_one_unique | (apply op_1429_mirror_symmetric_m_leafy_trees_n_one_unique <;> assumption) | (apply op_1429_mirror_symmetric_m_leafy_trees_n_one_unique <;> simp_all) | simpa using op_1429_mirror_symmetric_m_leafy_trees_n_one_unique)
