import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_two_sided_coloring

Topic: combinatorics   Node: 1f6f85e15091

Provenance: formalization of a published result. Source: arXiv:2611.12065, Definition 3.1

The two-sided face coloring B_n of T(n) coloring every front face black (true) and every back face white (false).
-/

/-- The two-sided coloring B_n of T(n). -/
def doubled_triangle_two_sided_coloring (n : ℕ) : DoubledTriangleFace n → Bool := fun f => match f with
  | .up front _ _ _ => front
  | .down front _ _ _ => front
