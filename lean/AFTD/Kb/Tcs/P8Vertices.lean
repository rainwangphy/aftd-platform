import AFTD.Prelude
import AFTD.Kb.Tcs.Q3Vertices

/-!
# p8_vertices

Topic: combinatorics   Node: 0aa1cc88e747

Provenance: formalization of a published result. Source: arXiv:2611.08819 Section 2

The set of 44 vectors in Fin 8 → ℤ defined as the union of the image of q3_vertices under (fun v => ![v 0, v 1, v 2, 0, 0, 0, -1, -1]), the image of q3_vertices under (fun v => ![0, 0, 0, v 0, v 1, v 2, -1, -1]), and the two vectors ![0, 0, 0, 0, 0, 0, -1, 2] and ![0, 0, 0, 0, 0, 0, 1, -1].
-/

/-- The 44 lattice points in ℤ^8 generating the 8-dimensional polytope P_8. -/
def p8_vertices : Finset (Fin 8 → ℤ) := (q3_vertices.image (fun v => ![v 0, v 1, v 2, 0, 0, 0, -1, -1])) ∪
  (q3_vertices.image (fun v => ![0, 0, 0, v 0, v 1, v 2, -1, -1])) ∪
  { ![0, 0, 0, 0, 0, 0, -1, 2], ![0, 0, 0, 0, 0, 0, 1, -1] }
