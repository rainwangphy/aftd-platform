import AFTD.Prelude

/-!
# simple_graph_clique_components_closed_neighborhood

Topic: combinatorics   Node: 8180525f41d7

Provenance: helper lemma. Component decomposition for op_1355_clique_components_variance_ge_bound.

In a graph whose connected components are cliques, a vertex closed neighborhood is its connected-component fiber.
-/

open scoped Classical

theorem simple_graph_clique_components_closed_neighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) (v : V) :
    insert v (G.neighborFinset v) =
      Finset.univ.filter (fun u => G.connectedComponentMk u = G.connectedComponentMk v) := by
  classical
  ext u
  simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | h)
    · rfl
    · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h).symm
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · right
      let c := G.connectedComponentMk v
      have hvc : v ∈ c.supp := (c.mem_supp_iff v).mpr rfl
      have huc : u ∈ c.supp := (c.mem_supp_iff u).mpr h
      exact hclique c hvc huc (Ne.symm huv)
