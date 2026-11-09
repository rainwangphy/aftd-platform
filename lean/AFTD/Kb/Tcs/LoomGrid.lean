import AFTD.Prelude

/-!
# loom_grid

Topic: graphs   Node: 3f859cc32a91

Provenance: formalization of a published result. Source: arXiv:2611.09627:360

The loom grid B_{r,c} has vertex set [r] × [c] × {-, +}, where within each column all pairs on opposite sides are adjacent, and between consecutive columns all pairs in the same row are adjacent.
-/

/-- The loom grid B_{r,c} has vertices in Fin r × Fin c × Bool with complete bipartite connections between sides in each column and horizontal connections between consecutive columns in the same row. -/
def loom_grid (r c : ℕ) : SimpleGraph (Fin r × Fin c × Bool) := SimpleGraph.fromRel fun u v =>
    (u.2.1 = v.2.1 ∧ u.2.2 = false ∧ v.2.2 = true) ∨
    (u.1 = v.1 ∧ u.2.1.val + 1 = v.2.1.val)
