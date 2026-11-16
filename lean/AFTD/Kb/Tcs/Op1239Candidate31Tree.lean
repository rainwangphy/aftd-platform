import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate31
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.Tcs.SimpleGraphOfEdgeList
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op_1239_candidate31_tree

Topic: combinatorics   Node: 7364ec4ee8f8

Provenance: helper lemma. OP-1239, arXiv:2611.07503, Problem 16; candidate from experiments 28663 and 28669.

The graph op_1239_candidate31 is a tree.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Op1239Graph31
instance adjacency : DecidableRel op_1239_candidate31.Adj := by
  unfold op_1239_candidate31
  infer_instance

theorem graph_degree : op_1239_candidate31.maxDegree ≤ 3 := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro v
  fin_cases v <;> decide

theorem graph_connected : op_1239_candidate31.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  use (0 : Fin 31)
  have h1 : op_1239_candidate31.Reachable 0 1 := (show op_1239_candidate31.Adj 0 1 from by decide).reachable
  have h11 : op_1239_candidate31.Reachable 0 11 := (show op_1239_candidate31.Adj 0 11 from by decide).reachable
  have h21 : op_1239_candidate31.Reachable 0 21 := (show op_1239_candidate31.Adj 0 21 from by decide).reachable
  have h2 : op_1239_candidate31.Reachable 0 2 := h1.trans (show op_1239_candidate31.Adj 1 2 from by decide).reachable
  have h4 : op_1239_candidate31.Reachable 0 4 := h1.trans (show op_1239_candidate31.Adj 1 4 from by decide).reachable
  have h12 : op_1239_candidate31.Reachable 0 12 := h11.trans (show op_1239_candidate31.Adj 11 12 from by decide).reachable
  have h14 : op_1239_candidate31.Reachable 0 14 := h11.trans (show op_1239_candidate31.Adj 11 14 from by decide).reachable
  have h22 : op_1239_candidate31.Reachable 0 22 := h21.trans (show op_1239_candidate31.Adj 21 22 from by decide).reachable
  have h24 : op_1239_candidate31.Reachable 0 24 := h21.trans (show op_1239_candidate31.Adj 21 24 from by decide).reachable
  have h3 : op_1239_candidate31.Reachable 0 3 := h2.trans (show op_1239_candidate31.Adj 2 3 from by decide).reachable
  have h5 : op_1239_candidate31.Reachable 0 5 := h4.trans (show op_1239_candidate31.Adj 4 5 from by decide).reachable
  have h6 : op_1239_candidate31.Reachable 0 6 := h4.trans (show op_1239_candidate31.Adj 4 6 from by decide).reachable
  have h13 : op_1239_candidate31.Reachable 0 13 := h12.trans (show op_1239_candidate31.Adj 12 13 from by decide).reachable
  have h15 : op_1239_candidate31.Reachable 0 15 := h14.trans (show op_1239_candidate31.Adj 14 15 from by decide).reachable
  have h16 : op_1239_candidate31.Reachable 0 16 := h14.trans (show op_1239_candidate31.Adj 14 16 from by decide).reachable
  have h23 : op_1239_candidate31.Reachable 0 23 := h22.trans (show op_1239_candidate31.Adj 22 23 from by decide).reachable
  have h25 : op_1239_candidate31.Reachable 0 25 := h24.trans (show op_1239_candidate31.Adj 24 25 from by decide).reachable
  have h26 : op_1239_candidate31.Reachable 0 26 := h24.trans (show op_1239_candidate31.Adj 24 26 from by decide).reachable
  have h7 : op_1239_candidate31.Reachable 0 7 := h6.trans (show op_1239_candidate31.Adj 6 7 from by decide).reachable
  have h9 : op_1239_candidate31.Reachable 0 9 := h6.trans (show op_1239_candidate31.Adj 6 9 from by decide).reachable
  have h17 : op_1239_candidate31.Reachable 0 17 := h16.trans (show op_1239_candidate31.Adj 16 17 from by decide).reachable
  have h19 : op_1239_candidate31.Reachable 0 19 := h16.trans (show op_1239_candidate31.Adj 16 19 from by decide).reachable
  have h27 : op_1239_candidate31.Reachable 0 27 := h26.trans (show op_1239_candidate31.Adj 26 27 from by decide).reachable
  have h29 : op_1239_candidate31.Reachable 0 29 := h26.trans (show op_1239_candidate31.Adj 26 29 from by decide).reachable
  have h8 : op_1239_candidate31.Reachable 0 8 := h7.trans (show op_1239_candidate31.Adj 7 8 from by decide).reachable
  have h10 : op_1239_candidate31.Reachable 0 10 := h9.trans (show op_1239_candidate31.Adj 9 10 from by decide).reachable
  have h18 : op_1239_candidate31.Reachable 0 18 := h17.trans (show op_1239_candidate31.Adj 17 18 from by decide).reachable
  have h20 : op_1239_candidate31.Reachable 0 20 := h19.trans (show op_1239_candidate31.Adj 19 20 from by decide).reachable
  have h28 : op_1239_candidate31.Reachable 0 28 := h27.trans (show op_1239_candidate31.Adj 27 28 from by decide).reachable
  have h30 : op_1239_candidate31.Reachable 0 30 := h29.trans (show op_1239_candidate31.Adj 29 30 from by decide).reachable
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30

theorem graph_edges : op_1239_candidate31.edgeFinset.card = 30 := by decide

theorem graph_tree : op_1239_candidate31.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨graph_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  simp [graph_edges]
end Op1239Graph31

theorem op_1239_candidate31_tree : op_1239_candidate31.IsTree := by
  exact Op1239Graph31.graph_tree
