import AFTD.Prelude

/-!
# digraph_trianglefree_deficit_sharp54_graph

Topic: graphs   Node: 29a2d818c34a

Provenance: helper lemma. Finite equality example for girth-dependent overlap accounting; experiments 13466 and 13467.

The cyclic 53-vertex digraph with out-steps 1, 8, 14, 16, 28, 32, 33, extended by a sink whose predecessors are 0, 1, 17, and 25.
-/

def digraph_trianglefree_deficit_sharp54_graph : Digraph (Fin 54) where
  Adj u v := (u.val < 53 ∧ v.val < 53 ∧
    (v.val + 53 - u.val) % 53 ∈ ({1,8,14,16,28,32,33} : Finset ℕ)) ∨
    ((u = 0 ∨ u = 1 ∨ u = 17 ∨ u = 25) ∧ v = 53)
