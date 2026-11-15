import AFTD.Prelude
import AFTD.Kb.Tcs.Op223WeightedSupportGraph
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op223_weighted_support_graph_is_tree

Topic: graphs   Node: 1eb2b1ccc4d6

Provenance: helper lemma. The finite weighted-shift counterexample candidate.

The support graph of the rational weighted-shift candidate is a tree.
-/

open SimpleGraph
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
lemma op223_weighted_support_edges : op223_weighted_support_graph.edgeSet =
    (({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(0,6), s(0,7), s(7,8), s(8,9), s(9,10), s(10,11), s(11,12)} : Finset (Sym2 (Fin 13))) : Set (Sym2 (Fin 13))) := by
  classical
  rw [op223_weighted_support_graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Sym2.mem_diagSet, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    have h : ∀ x ∈ ({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(0,6), s(0,7), s(7,8), s(8,9), s(9,10), s(10,11), s(11,12)} : Finset (Sym2 (Fin 13))), ¬ x.IsDiag := by decide
    apply h e
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he

theorem op223_weighted_support_graph_is_tree : op223_weighted_support_graph.IsTree := by
  classical
  have e01 : op223_weighted_support_graph.Adj 0 1 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e12 : op223_weighted_support_graph.Adj 1 2 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e23 : op223_weighted_support_graph.Adj 2 3 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e34 : op223_weighted_support_graph.Adj 3 4 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e45 : op223_weighted_support_graph.Adj 4 5 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e06 : op223_weighted_support_graph.Adj 0 6 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e07 : op223_weighted_support_graph.Adj 0 7 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e78 : op223_weighted_support_graph.Adj 7 8 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e89 : op223_weighted_support_graph.Adj 8 9 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e910 : op223_weighted_support_graph.Adj 9 10 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e1011 : op223_weighted_support_graph.Adj 10 11 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e1112 : op223_weighted_support_graph.Adj 11 12 := by simp [op223_weighted_support_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    intro x
    fin_cases x
    · exact Reachable.rfl
    · exact e01.reachable
    · exact e01.reachable.trans e12.reachable
    · exact (e01.reachable.trans e12.reachable).trans e23.reachable
    · exact ((e01.reachable.trans e12.reachable).trans e23.reachable).trans e34.reachable
    · exact (((e01.reachable.trans e12.reachable).trans e23.reachable).trans e34.reachable).trans e45.reachable
    · exact e06.reachable
    · exact e07.reachable
    · exact e07.reachable.trans e78.reachable
    · exact (e07.reachable.trans e78.reachable).trans e89.reachable
    · exact ((e07.reachable.trans e78.reachable).trans e89.reachable).trans e910.reachable
    · exact (((e07.reachable.trans e78.reachable).trans e89.reachable).trans e910.reachable).trans e1011.reachable
    · exact ((((e07.reachable.trans e78.reachable).trans e89.reachable).trans e910.reachable).trans e1011.reachable).trans e1112.reachable
  · rw [Nat.card_coe_set_eq, op223_weighted_support_edges, Set.ncard_coe_finset]
    norm_num [Finset.card_insert_eq_ite, Sym2.eq, Fin.ext_iff, Nat.card_eq_fintype_card]
