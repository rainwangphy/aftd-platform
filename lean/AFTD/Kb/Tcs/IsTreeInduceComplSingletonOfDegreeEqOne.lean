import AFTD.Prelude

/-!
# isTree_induce_compl_singleton_of_degree_eq_one

Topic: graphs   Node: 59e045ad2840

Provenance: helper lemma. arXiv:2611.04674 Lemma 2.1 (Pair preparation)

If G is a tree and v is a vertex of degree one, then the induced subgraph G[{v}ᶜ] obtained by deleting v is also a tree.
-/

/-- The induced subgraph obtained by removing a leaf (a vertex of degree 1) from a tree is a tree. -/
theorem isTree_induce_compl_singleton_of_degree_eq_one {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype ↑(G.neighborSet v)] (hG : G.IsTree) (hdeg : G.degree v = 1) :
    (G.induce ({v}ᶜ : Set V)).IsTree := ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hdeg, hG.isAcyclic.induce _⟩
