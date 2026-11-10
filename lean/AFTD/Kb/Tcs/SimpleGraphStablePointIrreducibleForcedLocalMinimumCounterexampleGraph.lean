import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStablePointIrreducibleForcedLocalMinimumCounterexampleEdges

/-!
# simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_graph

Topic: graphs   Node: 43e195a139ca

Provenance: helper lemma. step towards simple_graph_stable_point_irreducible_forced_local_minimum_counterexample

The nine-vertex witness graph with the 26 listed edges.
-/

/-- The nine-vertex witness graph, built from the explicit 26-edge set. -/
def simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_graph : SimpleGraph (Fin 9) := SimpleGraph.fromEdgeSet (↑simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_edges)
