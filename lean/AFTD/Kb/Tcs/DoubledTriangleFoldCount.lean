import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleEdgeFaces
import AFTD.Kb.Tcs.DoubledTriangleEdge
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_fold_count

Topic: combinatorics   Node: ae16cb5add8f

Provenance: formalization of a published result. Source: arXiv:2611.12065, Definition 2.1

The fold count of a face 2-coloring C of the doubled equilateral triangle triangulation T(n), defined as the number of edges e : DoubledTriangleEdge n whose two incident faces under doubled_triangle_edge_faces have different colors under C.
-/

/-- The fold count of a face coloring of T(n). -/
def doubled_triangle_fold_count {n : ℕ} (C : DoubledTriangleFace n → Bool) : ℕ := Finset.card (Finset.univ.filter (fun e : DoubledTriangleEdge n =>
    C (doubled_triangle_edge_faces e).1 ≠ C (doubled_triangle_edge_faces e).2))
