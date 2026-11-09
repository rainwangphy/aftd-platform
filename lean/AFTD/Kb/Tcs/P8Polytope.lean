import AFTD.Prelude
import AFTD.Kb.Tcs.P8Vertices

/-!
# p8_polytope

Topic: combinatorics   Node: b0cf10e9cf54

Provenance: formalization of a published result. Source: arXiv:2611.08819 Section 2

The 8-dimensional polytope P_8 in ℝ^8 defined as the convex hull of the image of p8_vertices under the coordinatewise integer-to-real coercion (fun z i => (z i : ℝ)).
-/

/-- The 8-dimensional polytope P_8 ⊂ ℝ^8 defined as the convex hull of p8_vertices. -/
def p8_polytope : Set (Fin 8 → ℝ) := convexHull ℝ ((fun z i => (z i : ℝ)) '' (p8_vertices : Set (Fin 8 → ℤ)))
