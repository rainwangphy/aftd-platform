import AFTD.Prelude

/-!
# simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_edges

Topic: graphs   Node: 37c7152054ce

Provenance: helper lemma. step towards simple_graph_stable_point_irreducible_forced_local_minimum_counterexample

The 26 edges of the nine-vertex witness graph, listed explicitly as unordered vertex pairs.
-/

/-- The 26-edge set of the nine-vertex witness graph. -/
def simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_edges : Finset (Sym2 (Fin 9)) := {s(0,1),s(0,2),s(0,3),s(0,5),s(1,2),s(1,3),s(1,4),s(1,5),s(1,6),s(1,7),
     s(2,3),s(2,4),s(2,5),s(2,6),s(2,8),s(3,4),s(3,5),s(3,6),s(3,7),s(3,8),
     s(4,5),s(4,6),s(5,6),s(5,7),s(6,7),s(6,8)}
