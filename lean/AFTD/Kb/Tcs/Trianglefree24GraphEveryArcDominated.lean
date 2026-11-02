import AFTD.Prelude
import AFTD.Kb.Tcs.Trianglefree24Graph

/-!
# trianglefree24_graph_every_arc_dominated

Topic: graphs   Node: e415d96fcf2b

Provenance: helper lemma. Finite check for experiment 12544.

Every arc of the explicit 24-vertex digraph has a common in-neighbor.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private instance trianglefree24_decAdj_every_arc_dominated : DecidableRel trianglefree24_graph.Adj := by
  intro u v
  unfold trianglefree24_graph
  infer_instance

theorem trianglefree24_graph_every_arc_dominated :
    ∀ u v : Fin 24, trianglefree24_graph.Adj u v →
      ∃ w, trianglefree24_graph.Adj w u ∧ trianglefree24_graph.Adj w v := by
  decide
