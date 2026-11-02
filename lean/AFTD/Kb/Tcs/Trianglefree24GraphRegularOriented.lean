import AFTD.Prelude
import AFTD.Kb.Tcs.Trianglefree24Graph

/-!
# trianglefree24_graph_regular_oriented

Topic: graphs   Node: aee871b82d43

Provenance: helper lemma. Finite check for experiment 12544.

The explicit 24-vertex digraph is loopless, oriented and 7-outregular.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private instance trianglefree24_decAdj : DecidableRel trianglefree24_graph.Adj := by
  intro u v
  unfold trianglefree24_graph
  infer_instance

theorem trianglefree24_graph_regular_oriented :
    (∀ v : Fin 24, (Finset.univ.filter fun w => trianglefree24_graph.Adj v w).card = 7) ∧
    (∀ v : Fin 24, ¬ trianglefree24_graph.Adj v v) ∧
    (∀ u v : Fin 24, trianglefree24_graph.Adj u v → ¬ trianglefree24_graph.Adj v u) := by
  decide
