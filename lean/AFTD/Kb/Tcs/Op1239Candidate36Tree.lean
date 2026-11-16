import AFTD.Prelude
import AFTD.Kb.Tcs.Op1239Candidate36
import AFTD.Kb.Tcs.SimpleGraphOfEdgeListDecidableRel
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op_1239_candidate36_tree

Topic: combinatorics   Node: 6d38b3834774

Provenance: helper lemma. Candidate for OP-1239; computations 28328 and 28332 checks the standard leaf-deletion recurrence from arXiv:2611.07503, Lemma 1.

The graph op_1239_candidate36 is a tree.
-/

namespace Op1239Tree36
instance : DecidableRel op_1239_candidate36.Adj := by
  unfold op_1239_candidate36
  exact simple_graph_of_edge_list_decidable_rel _

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem graph_connected : op_1239_candidate36.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  use (0 : Fin 36)
  have h1 : op_1239_candidate36.Reachable 0 1 := (show op_1239_candidate36.Adj 0 1 from by decide).reachable
  have h3 : op_1239_candidate36.Reachable 0 3 := (show op_1239_candidate36.Adj 0 3 from by decide).reachable
  have h8 : op_1239_candidate36.Reachable 0 8 := (show op_1239_candidate36.Adj 0 8 from by decide).reachable
  have h2 : op_1239_candidate36.Reachable 0 2 := h1.trans (show op_1239_candidate36.Adj 1 2 from by decide).reachable
  have h4 : op_1239_candidate36.Reachable 0 4 := h1.trans (show op_1239_candidate36.Adj 1 4 from by decide).reachable
  have h5 : op_1239_candidate36.Reachable 0 5 := h3.trans (show op_1239_candidate36.Adj 3 5 from by decide).reachable
  have h21 : op_1239_candidate36.Reachable 0 21 := h3.trans (show op_1239_candidate36.Adj 3 21 from by decide).reachable
  have h11 : op_1239_candidate36.Reachable 0 11 := h8.trans (show op_1239_candidate36.Adj 8 11 from by decide).reachable
  have h26 : op_1239_candidate36.Reachable 0 26 := h8.trans (show op_1239_candidate36.Adj 8 26 from by decide).reachable
  have h6 : op_1239_candidate36.Reachable 0 6 := h2.trans (show op_1239_candidate36.Adj 2 6 from by decide).reachable
  have h7 : op_1239_candidate36.Reachable 0 7 := h2.trans (show op_1239_candidate36.Adj 2 7 from by decide).reachable
  have h12 : op_1239_candidate36.Reachable 0 12 := h4.trans (show op_1239_candidate36.Adj 4 12 from by decide).reachable
  have h16 : op_1239_candidate36.Reachable 0 16 := h4.trans (show op_1239_candidate36.Adj 4 16 from by decide).reachable
  have h13 : op_1239_candidate36.Reachable 0 13 := h5.trans (show op_1239_candidate36.Adj 5 13 from by decide).reachable
  have h14 : op_1239_candidate36.Reachable 0 14 := h5.trans (show op_1239_candidate36.Adj 5 14 from by decide).reachable
  have h27 : op_1239_candidate36.Reachable 0 27 := h11.trans (show op_1239_candidate36.Adj 11 27 from by decide).reachable
  have h33 : op_1239_candidate36.Reachable 0 33 := h11.trans (show op_1239_candidate36.Adj 11 33 from by decide).reachable
  have h9 : op_1239_candidate36.Reachable 0 9 := h6.trans (show op_1239_candidate36.Adj 6 9 from by decide).reachable
  have h18 : op_1239_candidate36.Reachable 0 18 := h6.trans (show op_1239_candidate36.Adj 6 18 from by decide).reachable
  have h10 : op_1239_candidate36.Reachable 0 10 := h7.trans (show op_1239_candidate36.Adj 7 10 from by decide).reachable
  have h15 : op_1239_candidate36.Reachable 0 15 := h7.trans (show op_1239_candidate36.Adj 7 15 from by decide).reachable
  have h22 : op_1239_candidate36.Reachable 0 22 := h12.trans (show op_1239_candidate36.Adj 12 22 from by decide).reachable
  have h20 : op_1239_candidate36.Reachable 0 20 := h16.trans (show op_1239_candidate36.Adj 16 20 from by decide).reachable
  have h31 : op_1239_candidate36.Reachable 0 31 := h16.trans (show op_1239_candidate36.Adj 16 31 from by decide).reachable
  have h17 : op_1239_candidate36.Reachable 0 17 := h13.trans (show op_1239_candidate36.Adj 13 17 from by decide).reachable
  have h24 : op_1239_candidate36.Reachable 0 24 := h14.trans (show op_1239_candidate36.Adj 14 24 from by decide).reachable
  have h29 : op_1239_candidate36.Reachable 0 29 := h18.trans (show op_1239_candidate36.Adj 18 29 from by decide).reachable
  have h32 : op_1239_candidate36.Reachable 0 32 := h18.trans (show op_1239_candidate36.Adj 18 32 from by decide).reachable
  have h19 : op_1239_candidate36.Reachable 0 19 := h10.trans (show op_1239_candidate36.Adj 10 19 from by decide).reachable
  have h30 : op_1239_candidate36.Reachable 0 30 := h10.trans (show op_1239_candidate36.Adj 10 30 from by decide).reachable
  have h23 : op_1239_candidate36.Reachable 0 23 := h20.trans (show op_1239_candidate36.Adj 20 23 from by decide).reachable
  have h28 : op_1239_candidate36.Reachable 0 28 := h20.trans (show op_1239_candidate36.Adj 20 28 from by decide).reachable
  have h35 : op_1239_candidate36.Reachable 0 35 := h29.trans (show op_1239_candidate36.Adj 29 35 from by decide).reachable
  have h25 : op_1239_candidate36.Reachable 0 25 := h23.trans (show op_1239_candidate36.Adj 23 25 from by decide).reachable
  have h34 : op_1239_candidate36.Reachable 0 34 := h28.trans (show op_1239_candidate36.Adj 28 34 from by decide).reachable
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
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35

theorem graph_edges : op_1239_candidate36.edgeFinset.card = 35 := by decide


end Op1239Tree36

theorem op_1239_candidate36_tree : op_1239_candidate36.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨Op1239Tree36.graph_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  simp [Op1239Tree36.graph_edges]
