import AFTD.Prelude

/-!
# simple_graph_clique_components_independent_iff_injective

Topic: combinatorics   Node: b4060d554b55

Provenance: helper lemma. Component decomposition for op_1355_clique_components_variance_ge_bound.

In a graph whose connected components are cliques, a set is independent exactly when the component map is injective on it.
-/

open scoped Classical

theorem simple_graph_clique_components_independent_iff_injective {V : Type*} (G : SimpleGraph V)
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) (s : Set V) :
    G.IsIndepSet s ↔ s.InjOn G.connectedComponentMk := by
  constructor
  · intro h v hv w hw hvw
    by_contra hne
    have hadj : G.Adj v w := by
      let c := G.connectedComponentMk v
      have hvc : v ∈ c.supp := (c.mem_supp_iff v).mpr rfl
      have hwc : w ∈ c.supp := (c.mem_supp_iff w).mpr hvw.symm
      exact hclique c hvc hwc hne
    exact h hv hw hne hadj
  · intro h v hv w hw hne hadj
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    exact hne (h hv hw heq)
