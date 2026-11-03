import AFTD.Prelude

/-!
# simple_graph_categorical_prod

Topic: information   Node: 9f3ca50438cb

Provenance: formalization of a published result. Source: arXiv:2610.41977 Sec. 1

The categorical product (tensor product) G × H of two simple graphs G and H has vertex set V(G) × V(H), with an edge between (u₁, v₁) and (u₂, v₂) if and only if u₁ is adjacent to u₂ in G and v₁ is adjacent to v₂ in H.
-/

/-- The categorical (tensor) product of two simple graphs. -/
def simple_graph_categorical_prod {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) := {
  Adj := fun x y => G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm.symm := fun x y => by simp [SimpleGraph.adj_comm]
}
