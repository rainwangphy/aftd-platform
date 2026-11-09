import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleFreeLoomGridVert

/-!
# triangle_free_loom_grid

Topic: graphs   Node: 44f8e51219e5

Provenance: formalization of a published result. Source: arXiv:2611.09627:380

The triangle-free loom grid on the vertex type triangle_free_loom_grid_vert r c is the simple graph where two vertices u and v are adjacent iff they share the same column on opposite sides with different rows, or share the same row with columns differing by 1.
-/

/-- The triangle-free loom grid T_{r,c} with column edges between different rows on opposite sides in odd columns, and horizontal edges between consecutive columns in the same row. -/
def triangle_free_loom_grid (r c : ℕ) : SimpleGraph (triangle_free_loom_grid_vert r c) := SimpleGraph.fromRel fun u v =>
    (u.1.2.1 = v.1.2.1 ∧ u.1.2.2 = false ∧ v.1.2.2 = true ∧ u.1.1 ≠ v.1.1) ∨
    (u.1.1 = v.1.1 ∧ u.1.2.1.val + 1 = v.1.2.1.val)
