import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStablePointIrreducibleForcedLocalMinimumCounterexampleEdges
import AFTD.Kb.Tcs.SimpleGraphStablePointIrreducibleForcedLocalMinimumCounterexampleGraph

/-!
# simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_graph_decidable_rel

Topic: graphs   Node: 633ac7803d30

Provenance: helper lemma. step towards simple_graph_stable_point_irreducible_forced_local_minimum_counterexample

Adjacency in the witness graph is decidable, through membership in the explicit edge list.
-/

/-- Decidability of adjacency in the witness graph, reduced to the explicit edge list. -/
instance simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_graph_decidable_rel : DecidableRel simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_graph.Adj := fun a b => inferInstanceAs (Decidable (s(a, b) ∈ (↑simple_graph_stable_point_irreducible_forced_local_minimum_counterexample_edges : Set (Sym2 (Fin 9))) ∧ a ≠ b))
