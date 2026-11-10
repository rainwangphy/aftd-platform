import AFTD.Prelude

/-!
# simple_graph_stable_forced_k4_anchor_test_graph

Topic: graphs   Node: 719ac26ccdac

Provenance: helper lemma. step towards simple_graph_stable_forced_k4_anchor_unforced_counterexample

The witness graph of the counterexample: the join of the five-clique on {4,5,6,7,8} with the independent set {0,1,2,3}; two vertices are adjacent iff they are distinct and at least one of them is at least 4.
-/

/-- The join of K5 on {4,...,8} with the independent set {0,1,2,3} on Fin 9. -/
abbrev simple_graph_stable_forced_k4_anchor_test_graph : SimpleGraph (Fin 9) := SimpleGraph.fromRel (fun (_ : Fin 9) (y : Fin 9) => 4 ≤ y)
