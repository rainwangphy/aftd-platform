import AFTD.Prelude

/-!
# simple_graph_clique_polynomial

Topic: graphs   Node: b562c767f5c5

Provenance: formalization of a published result. Source: arXiv:2611.14430, Section 4

The clique polynomial $C_G(z) = \sum_{t=0}^{|V|} c_t(G) z^t$ of a finite simple graph $G$, where $c_t(G)$ is the number of cliques of order $t$ in $G$.
-/

/-- The clique polynomial of a finite simple graph, with coefficient of z^t equal to the number of cliques of size t. -/
noncomputable def simple_graph_clique_polynomial {V : Type*} [Fintype V] (G : SimpleGraph V) : Polynomial ℤ :=
  open scoped Classical in
  ∑ t ∈ Finset.range (Fintype.card V + 1), Polynomial.C ((G.cliqueFinset t).card : ℤ) * Polynomial.X ^ t
