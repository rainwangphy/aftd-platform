import AFTD.Prelude

/-!
# digraph_weighted_center_strict54_graph

Topic: graphs   Node: b0de6a193f95

Provenance: helper lemma. Strictness witness for the weighted center route; experiments 13477 and 13478.

The cyclic 53-vertex digraph with steps 1, 8, 14, 16, 28, 32, 33, extended by a new vertex with in-neighbors 0, 1, 17, 25 and out-neighbors 2, 4, 5, 8, 14, 15, 29.
-/

def digraph_weighted_center_strict54_graph : Digraph (Fin 54) where
  Adj u v := (u.val < 53 ∧ v.val < 53 ∧
    (v.val + 53 - u.val) % 53 ∈ ({1,8,14,16,28,32,33} : Finset ℕ)) ∨
    ((u = 0 ∨ u = 1 ∨ u = 17 ∨ u = 25) ∧ v = 53) ∨
    (u = 53 ∧ v ∈ ({2,4,5,8,14,15,29} : Finset (Fin 54)))
