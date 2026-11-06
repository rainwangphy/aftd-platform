import AFTD.Prelude

/-!
# simple_graph_stable_conflict_independence_leaf_two

Topic: graphs   Node: c9c92b2069fc

Provenance: helper lemma. step towards simple_graph_stable_conflict_independence_counterexample

The second leaf triangle {1,5,7} of the counterexample graph: the only triangle besides {1,3,7} that does not pass through the apex 0.
-/

/-- The leaf triangle {1,5,7} (edges {1,5}, {1,7}, {5,7}). -/
def simple_graph_stable_conflict_independence_leaf_two : Finset (Sym2 (Fin 11)) := {Sym2.mk (1 : Fin 11) 5, Sym2.mk (1 : Fin 11) 7, Sym2.mk (5 : Fin 11) 7}
