import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHighDegreeStablePointIrreducibleForcedExchangeBarrierCounterexampleEdges

/-!
# simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_graph

Topic: graphs   Node: 2c4bf54f6bf5

Provenance: helper lemma. step towards simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample

The witness graph on 12 vertices with the 54 listed edges.
-/

/-- The witness graph: the graph on Fin 12 with the 54 listed edges. -/
def simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_graph : SimpleGraph (Fin 12) := SimpleGraph.fromEdgeSet (↑simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_edges : Set (Sym2 (Fin 12)))
