import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphLocalFourWitness
import AFTD.Kb.Tcs.DigraphLocalSourceSet
import AFTD.Kb.Tcs.DigraphLocalSourceExpansion
import AFTD.Kb.Tcs.DigraphLocalFourWitnessSourcesSinks

/-!
# digraph_local_four_witness_combined_properties

Topic: graphs   Node: 7311226d54bb

Provenance: helper lemma. arXiv:2601.11847, Theorem 1.2 and Problem 5.2; accompanying certificate for the OP-337 local obstruction.

The explicit 24-vertex witness is source-free and oriented with maximum outdegree four; all sources after any closed out-neighborhood deletion are sinks, and the local expansion satisfies the 5/4 inequality at every vertex.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem digraph_local_four_witness_combined_properties :
    (∀ v, v ∉ digraph_local_four_witness v) ∧
    (∀ v, ∃ u, v ∈ digraph_local_four_witness u) ∧
    (∀ u v, v ∈ digraph_local_four_witness u → u ∉ digraph_local_four_witness v) ∧
    (∀ v, (digraph_local_four_witness v).card ≤ 4) ∧
    (∀ v, ∀ u ∈ digraph_local_source_set digraph_local_four_witness v,
      digraph_local_four_witness u = ∅) ∧
    (∀ v, 5 * (digraph_local_source_expansion digraph_local_four_witness v).card ≤
      4 * ((digraph_local_source_set digraph_local_four_witness v).card + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, digraph_local_four_witness_sources_sinks, ?_⟩
  · intro v; fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
  · intro u v; fin_cases u <;> fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
  · intro v; fin_cases v <;> decide
