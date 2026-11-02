import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorSevenBoundedIndegreeDegreeBound
import AFTD.Kb.Tcs.DigraphCommonPredecessorEdgesSevenClique
import AFTD.Kb.Tcs.ConnectedGraphIndepThreeDegree42SevenCliquesCardLe121

/-!
# digraph_common_predecessor_balanced_seven_card_le_121

Topic: graphs   Node: bdd1fbb4ab0e

Provenance: helper lemma. Auxiliary-graph transfer and counting steps for the OP-110 campaign.

A 7-outregular digraph with indegrees at most seven has at most 121 vertices if its common-predecessor graph is connected and has independence number at most three.
-/

private instance in478_digraph_common_predecessor_balanced_seven_card_le_121_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_balanced_seven_card_le_121 (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hinde : ∀ v, (Finset.univ.filter fun w => D.Adj w v).card ≤ 7)
    (hconn : (digraph_common_predecessor_graph D).Connected)
    (hindep : (digraph_common_predecessor_graph D).IndepSetFree 4) :
    Fintype.card α ≤ 121 := by
  exact connected_graph_indep_three_degree_42_seven_cliques_card_le_121 α
    (digraph_common_predecessor_graph D) hconn hindep (digraph_common_predecessor_seven_bounded_indegree_degree_bound α D hreg hinde)
    (digraph_common_predecessor_edges_seven_clique α D hreg)
