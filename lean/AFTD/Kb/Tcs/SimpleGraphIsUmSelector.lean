import AFTD.Prelude

/-!
# simple_graph_is_um_selector

Topic: graphs   Node: 5d7536ef72ef

Provenance: formalization of a published result. Source: arXiv:2611.23478, Definition 2

A UM-selector of width p in a graph G is a pair (S, φ) where S is an independent set in G and φ : S → {1, ..., p} such that for every vertex x in G, N[x] ∩ S is nonempty and the maximum of φ on N[x] ∩ S is attained by exactly one vertex.
-/

/-- A UM-selector of width p in G is an independent set S and a colouring φ : S → Fin p such that in every closed neighbourhood N[x] the maximum of φ on N[x] ∩ S is attained by exactly one vertex. -/
def simple_graph_is_um_selector {V : Type*} (G : SimpleGraph V) {p : ℕ}
    (S : Set V) (φ : ↥S → Fin p) : Prop := G.IsIndepSet S ∧
  ∀ x : V, ∃ u : ↥S, u.1 ∈ insert x (G.neighborSet x) ∧
    ∀ w : ↥S, w.1 ∈ insert x (G.neighborSet x) → w ≠ u → φ w < φ u
