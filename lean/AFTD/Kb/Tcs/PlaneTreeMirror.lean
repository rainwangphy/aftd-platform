import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree

/-!
# plane_tree_mirror

Topic: combinatorics   Node: 8b731328050a

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.3

The left-right mirror reflection involution τ on plane trees, recursively reversing child order.
-/

/-- Left-right mirror reflection involution on plane trees. -/
def plane_tree_mirror : PlaneTree → PlaneTree
  | .leaf => .leaf
  | .node cs => .node (cs.attach.map (fun ⟨c, _⟩ => plane_tree_mirror c) |>.reverse)
termination_by t => sizeOf t
