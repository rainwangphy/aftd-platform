import AFTD.Prelude

/-!
# simple_graph_endpoint_sum_edges

Topic: graphs   Node: b97f6dc40c8b

Provenance: formalization of a published result. Source: arXiv:2611.16338, Section 2

Given a finite simple graph G and a vertex labeling φ : V → ℕ, the finset simple_graph_endpoint_sum_edges G φ r consists of all edges uv of G such that the sum of the endpoint labels φ(u) + φ(v) equals r.
-/

/-- The finset of edges of G whose endpoint labels sum to r. -/
noncomputable def simple_graph_endpoint_sum_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) (φ : V → ℕ) (r : ℕ) : Finset (Sym2 V) :=
  open scoped Classical in
  G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e = r)
