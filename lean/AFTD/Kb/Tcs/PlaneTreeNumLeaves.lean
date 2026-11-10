import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree

/-!
# plane_tree_num_leaves

Topic: combinatorics   Node: c16393013515

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.2

The number of leaves of a plane tree T, denoted ℓ(T).
-/

/-- The number of leaves in a finite plane tree. -/
def plane_tree_num_leaves : PlaneTree → ℕ
  | .leaf => 1
  | .node cs => cs.attach.map (fun ⟨c, _⟩ => plane_tree_num_leaves c) |>.sum
termination_by t => sizeOf t
