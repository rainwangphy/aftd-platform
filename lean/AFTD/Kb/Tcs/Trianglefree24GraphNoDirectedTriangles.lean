import AFTD.Prelude
import AFTD.Kb.Tcs.Trianglefree24Graph

/-!
# trianglefree24_graph_no_directed_triangles

Topic: graphs   Node: 8fceeb9de60a

Provenance: helper lemma. Finite check for experiments 12542 and 12544.

The explicit 24-vertex digraph contains no directed triangle.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private instance trianglefree24_decAdj_no_directed_triangles : DecidableRel trianglefree24_graph.Adj := by
  intro u v
  unfold trianglefree24_graph
  infer_instance

theorem trianglefree24_graph_no_directed_triangles :
    ∀ u v w : Fin 24, trianglefree24_graph.Adj u v →
      trianglefree24_graph.Adj v w → trianglefree24_graph.Adj w u → False := by
  decide
