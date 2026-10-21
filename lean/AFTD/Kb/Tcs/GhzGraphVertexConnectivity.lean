import AFTD.Prelude

/-!
# ghz_graph_vertex_connectivity

Topic: quantum   Node: 9c7f04658888

Provenance: formalization of a published result. Source: arXiv:2610.22190 Section 1.1

The vertex connectivity κ(G) of a finite simple graph G = (V, E) is |V| - 1 if G is the complete graph, and otherwise the minimum cardinality of a vertex set T ⊆ V such that the induced subgraph on V \ T is disconnected (not preconnected).
-/

/-- The vertex connectivity κ(G) of a simple graph: the minimum size of a vertex set whose deletion disconnects G, or |V| - 1 for complete graphs. -/
noncomputable def ghz_graph_vertex_connectivity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  open scoped Classical in
  if G = ⊤ then Fintype.card V - 1
  else sInf { n : ℕ | ∃ T : Finset V, ¬ (G.induce (Tᶜ : Set V)).Preconnected ∧ n = T.card }
