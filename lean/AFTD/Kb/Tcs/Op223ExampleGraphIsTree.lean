import AFTD.Prelude
import AFTD.Kb.Tcs.Op223ExampleGraph
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op223_example_graph_is_tree

Topic: graphs   Node: cd8bb1ad77cc

Provenance: helper lemma. step towards op223_example_graph_sustainable

The eight-vertex example graph op223_example_graph is a tree.
-/

open SimpleGraph
open scoped Classical

set_option maxHeartbeats 1000000 in
lemma op223_example_edges : op223_example_graph.edgeSet =
    (({s(0,1), s(0,4), s(0,7), s(1,2), s(2,3), s(4,5), s(4,6)} : Finset (Sym2 (Fin 8))) : Set (Sym2 (Fin 8))) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    fin_cases a <;> fin_cases b <;>
      simp [op223_example_graph, SimpleGraph.mem_edgeSet, SimpleGraph.fromEdgeSet_adj, Sym2.eq]

/-- The eight-vertex example graph op223_example_graph is a tree. -/
theorem op223_example_graph_is_tree : op223_example_graph.IsTree := by
  classical
  have e01 : op223_example_graph.Adj 0 1 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e04 : op223_example_graph.Adj 0 4 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e07 : op223_example_graph.Adj 0 7 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e12 : op223_example_graph.Adj 1 2 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e23 : op223_example_graph.Adj 2 3 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e45 : op223_example_graph.Adj 4 5 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e46 : op223_example_graph.Adj 4 6 := by simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    intro x; fin_cases x
    · exact Reachable.rfl
    · exact e01.reachable
    · exact e01.reachable.trans e12.reachable
    · exact (e01.reachable.trans e12.reachable).trans e23.reachable
    · exact e04.reachable
    · exact e04.reachable.trans e45.reachable
    · exact e04.reachable.trans e46.reachable
    · exact e07.reachable
  · rw [Nat.card_coe_set_eq, op223_example_edges, Set.ncard_coe_finset]
    norm_num [Finset.card_insert_eq_ite, Sym2.eq, Fin.ext_iff, Nat.card_eq_fintype_card]
