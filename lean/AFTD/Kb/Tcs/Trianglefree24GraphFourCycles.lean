import AFTD.Prelude
import AFTD.Kb.Tcs.Trianglefree24Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# trianglefree24_graph_four_cycles

Topic: graphs   Node: e7cb4c30ebc8

Provenance: helper lemma. Explicit cycles in experiment 12544.

Four displayed pairwise disjoint four-vertex subsets of the explicit 24-vertex digraph are directed cycles.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private instance trianglefree24_decAdj_four_cycles : DecidableRel trianglefree24_graph.Adj := by
  intro u v
  unfold trianglefree24_graph
  infer_instance

theorem trianglefree24_graph_four_cycles :
    digraph_directed_cycle_on trianglefree24_graph ({0,1,2,3} : Finset (Fin 24)) ∧
    digraph_directed_cycle_on trianglefree24_graph ({4,5,6,7} : Finset (Fin 24)) ∧
    digraph_directed_cycle_on trianglefree24_graph ({8,9,10,11} : Finset (Fin 24)) ∧
    digraph_directed_cycle_on trianglefree24_graph ({12,13,14,15} : Finset (Fin 24)) := by
  exact ⟨⟨[0,1,2,3], by decide⟩, ⟨[4,5,6,7], by decide⟩,
    ⟨[8,9,10,11], by decide⟩, ⟨[12,13,14,15], by decide⟩⟩
