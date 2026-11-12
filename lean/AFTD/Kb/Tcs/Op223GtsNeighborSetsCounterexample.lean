import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph

/-!
# op223_gts_neighbor_sets_counterexample

Topic: graphs   Node: a29ea5a9c636

Provenance: original. Related work: arXiv:2610.17078 Open Problem 6.1; counterexamples to auxiliary statements

There is a graph on four vertices with adjacent u and v and a third vertex x whose neighbor set changes after the generalized tree shift from v to u.
-/

open SimpleGraph
open scoped Classical

theorem op223_gts_neighbor_sets_counterexample :
    ∃ (T : SimpleGraph (Fin 4)) (u v x : Fin 4),
      T.Adj u v ∧ x ≠ u ∧ x ≠ v ∧
      (gts_graph T u v u).neighborSet x ≠ T.neighborSet x := by
  refine ⟨SimpleGraph.pathGraph 4, 1, 2, 3, ?_, by decide, by decide, ?_⟩
  · norm_num [SimpleGraph.pathGraph_adj]
  · intro h
    have hv : (SimpleGraph.pathGraph 4).Adj 3 2 := by norm_num [SimpleGraph.pathGraph_adj]
    have hnew : (gts_graph (SimpleGraph.pathGraph 4) 1 2 1).Adj 3 2 := by
      have hm : (2 : Fin 4) ∈ (SimpleGraph.pathGraph 4).neighborSet 3 := hv
      rw [← h] at hm
      exact hm
    simp [gts_graph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
      SimpleGraph.fromEdgeSet_adj, SimpleGraph.pathGraph_adj, Sym2.eq, Fin.ext_iff] at hnew
    specialize hnew 3
    norm_num at hnew
