import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleVertexFaces
import AFTD.Kb.Tcs.DoubledTriangleVertex
import AFTD.Kb.Tcs.DoubledTriangleFace

/-!
# doubled_triangle_is_good_coloring

Topic: combinatorics   Node: ca98ddf8baec

Provenance: formalization of a published result. Source: arXiv:2611.12065, Definition 2.1

A face 2-coloring of T(n) is good if at every vertex, the number of black faces is congruent to the number of white faces modulo 3.
-/

/-- Predicate for a face coloring of T(n) to be a good coloring. -/
def doubled_triangle_is_good_coloring {n : ℕ} (C : DoubledTriangleFace n → Bool) : Prop := ∀ v : DoubledTriangleVertex n,
    let faces := doubled_triangle_vertex_faces v
    let b := (faces.filter (fun f => C f = true)).card
    let w := (faces.filter (fun f => C f = false)).card
    (b : ℤ) ≡ (w : ℤ) [ZMOD 3]
