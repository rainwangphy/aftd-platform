import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphLocalFourWitness
import AFTD.Kb.Tcs.DigraphLocalSourceSet

/-!
# digraph_local_four_witness_sources_sinks

Topic: graphs   Node: 184273a6cf72

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; arXiv:2601.11847, Problem 5.2.

For the explicit 24-vertex maximum-outdegree-four witness, every source left after deleting a closed out-neighborhood is a sink.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem digraph_local_four_witness_sources_sinks :
    ∀ v, ∀ u ∈ digraph_local_source_set digraph_local_four_witness v,
      digraph_local_four_witness u = ∅ := by
  intro v
  fin_cases v <;> decide
