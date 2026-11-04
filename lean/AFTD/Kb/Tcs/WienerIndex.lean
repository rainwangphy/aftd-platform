import AFTD.Prelude

/-!
# wiener_index

Topic: graphs   Node: f5c27f22e16b

Provenance: formalization of a published result. Source: arXiv:2611.01808 Section 1, p. 3; Wiener (1947)

The Wiener index of a finite simple graph G is the sum of the shortest-path distances between all unordered pairs of vertices in G.
-/

/-- The Wiener index of a finite simple graph, defined as the sum of distances over all unordered pairs of vertices. -/
noncomputable def wiener_index {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := ∑ e : Sym2 V, Sym2.lift ⟨fun u v => G.dist u v, fun _ _ => G.dist_comm⟩ e
