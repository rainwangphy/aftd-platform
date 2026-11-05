import AFTD.Prelude

/-!
# coord_shift_edge_cond

Topic: combinatorics   Node: b104c5b12e47

Provenance: formalization of a published result. Source: arXiv:2611.05261 equation (4)

A pair of vectors (x, y) satisfies the edge condition for a subset S of ZMod p if y_j - x_j is in S for all coordinates j < d - 1, and y_{d-1} = x_{d-1} at the final coordinate.
-/

/-- Edge condition on pairs (x, y) in the coordinate-shift hypergraph H(p, d, S). -/
def coord_shift_edge_cond {p d : ℕ} (S : Set (ZMod p)) (x y : Fin d → ZMod p) : Prop := (∀ (i : Fin d), i.val + 1 < d → y i - x i ∈ S) ∧
   (∀ (i : Fin d), i.val + 1 = d → y i = x i)
