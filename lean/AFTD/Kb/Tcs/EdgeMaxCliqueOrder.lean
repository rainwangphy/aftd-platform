import AFTD.Prelude

/-!
# edge_max_clique_order

Topic: graphs   Node: 8b7efb6f917e

Provenance: formalization of a published result. Source: arXiv:2611.30029, Section 1.1

For a finite simple graph G and an edge e represented as an unordered pair in Sym2 V, edge_max_clique_order G e is the maximum cardinality of a clique in G containing both endpoints of e.
-/

/-- The maximum order of a clique in G containing an edge e. -/
noncomputable def edge_max_clique_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) : ℕ := open Classical in
  Finset.sup (Finset.univ.filter fun (s : Finset V) => G.IsClique (s : Set V) ∧ e.toFinset ⊆ s) Finset.card
