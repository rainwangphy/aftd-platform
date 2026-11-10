import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree

/-!
# plane_tree_subtrees

Topic: combinatorics   Node: e646a9c6d617

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.2

The collection of all rooted subtrees T_v of a plane tree T.
-/

/-- The list of all full rooted subtrees of a plane tree. -/
def plane_tree_subtrees : PlaneTree → List PlaneTree
  | .leaf => [.leaf]
  | .node cs => .node cs :: (cs.attach.flatMap (fun ⟨c, _⟩ => plane_tree_subtrees c))
termination_by t => sizeOf t
