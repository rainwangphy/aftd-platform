import AFTD.Prelude

/-!
# digraph_overlap_sharp_eight_graph

Topic: graphs   Node: 35752aaae3fc

Provenance: helper lemma. Explicit witness for the overlap collision-count route to OP-110; experiment 13163.

The oriented graph on eight vertices obtained from the cyclic graph on seven vertices with steps 1, 2 and 4 by adding a sink with predecessors 0, 1 and 5.
-/

def digraph_overlap_sharp_eight_graph : Digraph (Fin 8) :=
  ⟨fun u v =>
    (u.val < 7 ∧ v.val < 7 ∧
      (v.val + 7 - u.val) % 7 ∈ ({1, 2, 4} : Finset ℕ)) ∨
    ((u = 0 ∨ u = 1 ∨ u = 5) ∧ v = 7)⟩
