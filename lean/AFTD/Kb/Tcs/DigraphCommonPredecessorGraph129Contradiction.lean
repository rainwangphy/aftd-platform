import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraphEdgeCountLe
import AFTD.Kb.Tcs.ConnectedGraph129IndependenceThreeEdgeBound

/-!
# digraph_common_predecessor_graph_129_contradiction

Topic: graphs   Node: 4c1f5cad8f14

Provenance: helper lemma. The final auxiliary-graph counting step toward the 128-vertex minimum-counterexample bound for OP-110.

No digraph on 129 vertices can have outdegree at most seven while its common-predecessor graph is connected and has no independent set of size four.
-/

private instance {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_graph_129_contradiction
    (D : Digraph (Fin 129)) [DecidableRel D.Adj]
    (hdeg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card ≤ 7)
    (hconn : (digraph_common_predecessor_graph D).Connected)
    (hindep : (digraph_common_predecessor_graph D).IndepSetFree 4) : False := by
  have hlow := connected_graph_129_independence_three_edge_bound
    (digraph_common_predecessor_graph D) hconn hindep
  have hupper := digraph_common_predecessor_graph_edge_count_le (Fin 129) D hdeg
  norm_num at hupper
  omega
