import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSets
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order_eq_avg_of_isolated

Topic: graphs   Node: 9f107d5a9166

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

If v is an isolated vertex of G (deg v = 0), then avd_v(G) = avd(G): every dominating set contains v, so the dominating sets containing v are exactly all dominating sets. This is what reduces the local statement for a graph 'with no isolated vertex except possibly v' to the global one.
-/

/-- For an isolated vertex v every dominating set already contains v, so the local and global averages coincide. This is the identity that turns the isolated-vertex case of any local statement into a global one. -/
theorem simple_graph_local_avg_dominating_order_eq_avg_of_isolated {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (hv : G.degree v = 0) :
    simple_graph_local_avg_dominating_order G v = simple_graph_avg_dominating_order G := by
  have hiso : G.IsIsolated v := (SimpleGraph.degree_eq_zero G v).1 hv
  have hset : simple_graph_dominating_sets_containing G v = simple_graph_dominating_sets G := by
    ext S
    simp only [simple_graph_dominating_sets_containing, simple_graph_dominating_sets,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hvS, hdom⟩
      exact hdom
    · intro hdom
      refine ⟨?_, hdom⟩
      rcases hdom v with hvS | ⟨u, hu, hadj⟩
      · exact hvS
      · exfalso
        exact hiso u hadj.symm
  simp only [simple_graph_local_avg_dominating_order, simple_graph_avg_dominating_order, hset]
