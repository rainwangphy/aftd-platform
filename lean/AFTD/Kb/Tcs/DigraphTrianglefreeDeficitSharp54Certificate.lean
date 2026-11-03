import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphTrianglefreeDeficitSharp54Graph
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_trianglefree_deficit_sharp54_certificate

Topic: graphs   Node: 2288a74a49ba

Provenance: helper lemma. Finite equality example for girth-dependent overlap accounting; experiments 13466 and 13467.

The displayed 54-vertex digraph is loopless, oriented, triangle-free, and arc-dominated. Its total positive outdegree-minus-indegree deficit is four and its repeated common-predecessor incidence count is three.
-/

instance sharp54_decAdj : DecidableRel digraph_trianglefree_deficit_sharp54_graph.Adj := by
  intro u v; unfold digraph_trianglefree_deficit_sharp54_graph; infer_instance

instance sharp54_cp_decAdj :
    DecidableRel (digraph_common_predecessor_graph digraph_trianglefree_deficit_sharp54_graph).Adj := by
  intro u v; unfold digraph_common_predecessor_graph; infer_instance

set_option maxHeartbeats 1000000 in
theorem sharp54_cp_degree_sum :
    ∑ v : Fin 54, (Finset.univ.filter fun w =>
      (digraph_common_predecessor_graph digraph_trianglefree_deficit_sharp54_graph).Adj v w).card = 2276 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem sharp54_triangle_free : ∀ u v w, digraph_trianglefree_deficit_sharp54_graph.Adj u v → digraph_trianglefree_deficit_sharp54_graph.Adj v w → ¬ digraph_trianglefree_deficit_sharp54_graph.Adj w u := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem sharp54_arc_dominated : ∀ u v, digraph_trianglefree_deficit_sharp54_graph.Adj u v → ∃ p, digraph_trianglefree_deficit_sharp54_graph.Adj p u ∧ digraph_trianglefree_deficit_sharp54_graph.Adj p v := by
  decide +kernel

theorem digraph_trianglefree_deficit_sharp54_certificate :
    (∀ u, ¬ digraph_trianglefree_deficit_sharp54_graph.Adj u u) ∧
    (∀ u v, digraph_trianglefree_deficit_sharp54_graph.Adj u v →
      ¬ digraph_trianglefree_deficit_sharp54_graph.Adj v u) ∧
    (∀ u v w, digraph_trianglefree_deficit_sharp54_graph.Adj u v →
      digraph_trianglefree_deficit_sharp54_graph.Adj v w →
      ¬ digraph_trianglefree_deficit_sharp54_graph.Adj w u) ∧
    (∀ u v, digraph_trianglefree_deficit_sharp54_graph.Adj u v → ∃ p,
      digraph_trianglefree_deficit_sharp54_graph.Adj p u ∧
      digraph_trianglefree_deficit_sharp54_graph.Adj p v) ∧
    (∑ v : Fin 54, ((Finset.univ.filter fun w => digraph_trianglefree_deficit_sharp54_graph.Adj v w).card -
      (Finset.univ.filter fun w => digraph_trianglefree_deficit_sharp54_graph.Adj w v).card)) = 4 ∧
    ((∑ v : Fin 54, Nat.choose (Finset.univ.filter fun w =>
      digraph_trianglefree_deficit_sharp54_graph.Adj v w).card 2) -
        (digraph_common_predecessor_graph digraph_trianglefree_deficit_sharp54_graph).edgeFinset.card) = 3 := by
  refine ⟨by decide +kernel, by decide +kernel, sharp54_triangle_free, sharp54_arc_dominated,
    by decide +kernel, ?_⟩
  have h1 := (digraph_common_predecessor_graph digraph_trianglefree_deficit_sharp54_graph).sum_degrees_eq_twice_card_edges
  have h2 : ∑ v : Fin 54, (digraph_common_predecessor_graph digraph_trianglefree_deficit_sharp54_graph).degree v = 2276 := by
    rw [← sharp54_cp_degree_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have h3 : ∑ v : Fin 54, Nat.choose (Finset.univ.filter fun w => digraph_trianglefree_deficit_sharp54_graph.Adj v w).card 2 = 1141 := by
    decide +kernel
  omega
