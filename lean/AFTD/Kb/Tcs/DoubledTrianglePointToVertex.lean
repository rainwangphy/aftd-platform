import AFTD.Prelude
import AFTD.Kb.Tcs.DoubledTriangleVertex

/-!
# doubled_triangle_point_to_vertex

Topic: combinatorics   Node: a6c4abdfa8b6

Provenance: formalization of a published result. Source: arXiv:2611.12065, Section 2.3

Map a lattice point (i, j) in the triangle of side n to the corresponding vertex of T(n), identifying front and back on the boundary.
-/

/-- Map a lattice point in the triangle to the corresponding vertex of T(n). -/
def doubled_triangle_point_to_vertex {n : ℕ} (front : Bool) (i j : Fin (n + 1)) (h : (i : ℕ) + j ≤ n) : DoubledTriangleVertex n := if h_bd : (i : ℕ) = 0 ∨ (j : ℕ) = 0 ∨ (i : ℕ) + j = n then
    DoubledTriangleVertex.boundary i j h h_bd
  else
    have hi : 0 < (i : ℕ) := by omega
    have hj : 0 < (j : ℕ) := by omega
    have h_lt : (i : ℕ) + j < n := by omega
    DoubledTriangleVertex.interior front i j hi hj h_lt
