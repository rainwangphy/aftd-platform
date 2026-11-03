import AFTD.Prelude

/-!
# digraph_two_overlap_counterexample_graph

Topic: graphs   Node: 581210e378cf

Provenance: helper lemma. The finite counterexample to the 2z good-center route for OP-110, experiments 13185 and 13186.

The explicit 13-vertex oriented digraph listed by the recorded finite counterexample.
-/

def digraph_two_overlap_counterexample_graph : Digraph (Fin 13) :=
  ⟨fun u v => (u, v) ∈ ({(0, 1), (0, 2), (0, 4), (0, 7), (0, 8), (0, 10), (0, 12), (1, 2), (1, 3), (1, 5), (1, 7), (2, 3), (2, 4), (2, 6), (2, 11), (3, 0), (3, 4), (3, 5), (3, 8), (4, 1), (4, 5), (4, 6), (4, 12), (5, 0), (5, 2), (5, 6), (5, 7), (5, 9), (6, 0), (6, 1), (6, 3), (6, 11), (6, 12), (7, 3), (7, 8), (7, 9), (8, 5), (8, 9), (8, 10), (9, 0), (9, 10), (10, 1), (11, 0), (12, 2), (12, 11)} : Finset (Fin 13 × Fin 13))⟩
