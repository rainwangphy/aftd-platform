import AFTD.Prelude

/-!
# triangle_free_loom_grid_vert

Topic: graphs   Node: 2c316f8f6514

Provenance: formalization of a published result. Source: arXiv:2611.09627:377

For natural numbers r and c, triangle_free_loom_grid_vert r c is the subtype of elements v in Fin r × Fin c × Bool such that v.2.2 = false or (v.2.2 = true and v.2.1.val + 1 is odd).
-/

/-- The vertex subtype of the triangle-free loom grid T_{r,c}, consisting of elements in Fin r × Fin c × Bool with side false or with side true and 1-based column index (j + 1) odd. -/
def triangle_free_loom_grid_vert (r c : ℕ) : Type := {v : Fin r × Fin c × Bool // v.2.2 = false ∨ (v.2.2 = true ∧ Odd (v.2.1.val + 1))}
