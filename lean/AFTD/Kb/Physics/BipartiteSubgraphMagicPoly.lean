import AFTD.Prelude

/-!
# bipartite_subgraph_magic_poly

Topic: quantum_mechanics   Node: b66bccb3b94c

Provenance: formalization of a published result. Source: OP-1695

For a finite simple graph G = (V, E), the bipartite subgraph magic polynomial is 8^{-|V|} times the sum over all edge subsets A ⊆ E such that (V, A) is bipartite of (-2)^{|A|} 8^{k(V,A)}, where k(V,A) is the number of connected components of the spanning subgraph (V, A).
-/

open scoped Classical in
/-- The bipartite subgraph polynomial 8^{-|V|} ∑_{A ⊆ E, (V,A) bipartite} (-2)^{|A|} 8^{k(V,A)}. -/
noncomputable def bipartite_subgraph_magic_poly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := (1 / (8 ^ Fintype.card V : ℝ)) *
    ∑ A ∈ G.edgeFinset.powerset,
      if (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).IsBipartite then
        ((-2 : ℝ) ^ A.card) * (8 : ℝ) ^ (Fintype.card (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).ConnectedComponent)
      else 0
