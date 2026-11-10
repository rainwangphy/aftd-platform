import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleFaceVertices
import AFTD.Kb.Tcs.DoubledTriangleVertex
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_vertex_faces

Topic: combinatorics   Node: bf37bdb003de

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.1

The set of faces incident to a vertex of the doubled equilateral triangle triangulation T(n).
-/

/-- The set of faces incident to a vertex of T(n). -/
def doubled_triangle_vertex_faces {n : ℕ} (v : DoubledTriangleVertex n) : Finset (DoubledTriangleFace n) := Finset.univ.filter (fun f => v ∈ doubled_triangle_face_vertices f)
