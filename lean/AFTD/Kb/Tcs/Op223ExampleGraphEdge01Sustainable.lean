import AFTD.Prelude
import AFTD.Kb.Tcs.Op223ExampleGraph
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.Op223FirstReplacementSpectralLower
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.Tcs.Op223ExampleSpectralUpper
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op223_example_graph_edge_01_sustainable

Topic: graphs   Node: b6224771985d

Provenance: helper lemma. step towards op223_example_graph_sustainable

Edge 0-1 in op223_example_graph is sustainable.
-/

open SimpleGraph
open scoped Classical ENNReal

set_option maxHeartbeats 5000000 in
lemma op223_first_replacement_edges : example_witness_graph.edgeSet =
    (({s(0,4), s(0,7), s(1,2), s(2,3), s(2,4), s(4,5), s(4,6)} : Finset (Sym2 (Fin 8))) : Set (Sym2 (Fin 8))) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    fin_cases a <;> fin_cases b <;>
      simp [example_witness_graph, op223_example_graph, SimpleGraph.mem_edgeSet,
        SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]

theorem op223_first_replacement_tree : example_witness_graph.IsTree := by
  classical
  have e04 : example_witness_graph.Adj 0 4 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e07 : example_witness_graph.Adj 0 7 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e12 : example_witness_graph.Adj 1 2 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e23 : example_witness_graph.Adj 2 3 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e24 : example_witness_graph.Adj 2 4 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e45 : example_witness_graph.Adj 4 5 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have e46 : example_witness_graph.Adj 4 6 := by simp [example_witness_graph, op223_example_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    intro x; fin_cases x
    · exact Reachable.rfl
    · exact (e04.reachable.trans e24.symm.reachable).trans e12.symm.reachable
    · exact e04.reachable.trans e24.symm.reachable
    · exact (e04.reachable.trans e24.symm.reachable).trans e23.reachable
    · exact e04.reachable
    · exact e04.reachable.trans e45.reachable
    · exact e04.reachable.trans e46.reachable
    · exact e07.reachable
  · rw [Nat.card_coe_set_eq, op223_first_replacement_edges, Set.ncard_coe_finset]
    norm_num [Finset.card_insert_eq_ite, Sym2.eq, Fin.ext_iff, Nat.card_eq_fintype_card]

/-- Edge 0-1 in op223_example_graph is sustainable. -/
theorem op223_example_graph_edge_01_sustainable : is_sustainable_edge op223_example_graph s(0, 1) := by
  refine ⟨?_, s(4,2), ?_, ?_, ?_⟩
  · simp [SimpleGraph.mem_edgeSet, op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  · simp [SimpleGraph.mem_edgeSet, op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq, Fin.ext_iff]
  · exact op223_first_replacement_tree
  · exact le_trans op223_example_spectral_upper (le_of_lt op223_first_replacement_spectral_lower)
