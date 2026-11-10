import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree

/-!
# plane_tree_num_internal

Topic: combinatorics   Node: bf0147b2cada

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.2

The number of internal vertices of a plane tree T, denoted n(T).
-/

/-- The number of internal vertices in a finite plane tree. -/
def plane_tree_num_internal : PlaneTree → ℕ
  | .leaf => 0
  | .node cs => 1 + (cs.attach.map (fun ⟨c, _⟩ => plane_tree_num_internal c) |>.sum)
termination_by t => sizeOf t
