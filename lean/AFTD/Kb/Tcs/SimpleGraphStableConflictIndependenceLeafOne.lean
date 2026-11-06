import AFTD.Prelude

/-!
# simple_graph_stable_conflict_independence_leaf_one

Topic: graphs   Node: eb78ef28ccdb

Provenance: helper lemma. step towards simple_graph_stable_conflict_independence_counterexample

The first leaf triangle {1,3,7} of the counterexample graph: the only triangle besides {1,5,7} that does not pass through the apex 0.
-/

/-- The leaf triangle {1,3,7} (edges {1,3}, {1,7}, {3,7}). -/
def simple_graph_stable_conflict_independence_leaf_one : Finset (Sym2 (Fin 11)) := {Sym2.mk (1 : Fin 11) 3, Sym2.mk (1 : Fin 11) 7, Sym2.mk (3 : Fin 11) 7}
