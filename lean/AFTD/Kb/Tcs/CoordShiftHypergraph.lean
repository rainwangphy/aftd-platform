import AFTD.Prelude
import AFTD.Kb.Tcs.CoordShiftZ
import AFTD.Kb.Tcs.CoordShiftEdgeCond

/-!
# coord_shift_hypergraph

Topic: combinatorics   Node: 53c7af758e6b

Provenance: formalization of a published result. Source: arXiv:2611.05261 Section 2

The tripartite 3-uniform hypergraph H(p, d, S) has vertex parts {i} × (ZMod p)^d for i in Fin 3, with edges {(0, x), (1, y), (2, z(x,y))} for all pairs (x, y) satisfying the edge condition with respect to S.
-/

/-- The tripartite 3-uniform hypergraph H(p, d, S) on vertex set Fin 3 × ((Fin d) → ZMod p). -/
def coord_shift_hypergraph (p d : ℕ) (S : Set (ZMod p)) : Set (Finset (Fin 3 × (Fin d → ZMod p))) := { e | ∃ x y : Fin d → ZMod p, coord_shift_edge_cond S x y ∧ e = {(0, x), (1, y), (2, coord_shift_z x y)} }
