import AFTD.Prelude
import AFTD.Kb.Tcs.Op223WeightedElevenGraph
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op223_weighted_eleven_graph_is_tree

Topic: graphs   Node: bb8ededd4869

Provenance: helper lemma. The finite rational weighted-shift candidate.

The support graph of the eleven-vertex rational weighted-shift candidate is a tree.
-/

open SimpleGraph
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
lemma op223_weighted_eleven_edges : op223_weighted_eleven_graph.edgeSet =
    (({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(0,6), s(0,7), s(7,8), s(8,9), s(0,10)} : Finset (Sym2 (Fin 11))) : Set (Sym2 (Fin 11))) := by
  classical
  rw [op223_weighted_eleven_graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Sym2.mem_diagSet, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    have h : ∀ x ∈ ({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(0,6), s(0,7), s(7,8), s(8,9), s(0,10)} : Finset (Sym2 (Fin 11))), ¬ x.IsDiag := by decide
    apply h e
    simpa only [Finset.mem_insert, Finset.mem_singleton] using he

theorem op223_weighted_eleven_graph_is_tree : op223_weighted_eleven_graph.IsTree := by
  classical
  have e01 : op223_weighted_eleven_graph.Adj 0 1 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e12 : op223_weighted_eleven_graph.Adj 1 2 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e23 : op223_weighted_eleven_graph.Adj 2 3 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e34 : op223_weighted_eleven_graph.Adj 3 4 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e45 : op223_weighted_eleven_graph.Adj 4 5 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e06 : op223_weighted_eleven_graph.Adj 0 6 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e07 : op223_weighted_eleven_graph.Adj 0 7 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e78 : op223_weighted_eleven_graph.Adj 7 8 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e89 : op223_weighted_eleven_graph.Adj 8 9 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e010 : op223_weighted_eleven_graph.Adj 0 10 := by simp [op223_weighted_eleven_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
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
    · exact e010.reachable
  · rw [Nat.card_coe_set_eq, op223_weighted_eleven_edges, Set.ncard_coe_finset]
    norm_num [Finset.card_insert_eq_ite, Sym2.eq, Fin.ext_iff, Nat.card_eq_fintype_card]
