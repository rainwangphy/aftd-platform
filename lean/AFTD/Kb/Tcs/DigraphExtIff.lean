import AFTD.Prelude

/-!
# digraph_ext_iff

Topic: graphs   Node: 79b051367dfb

Provenance: helper lemma. step towards three_connected_plane_eulerian_arborescence_minimizers_alternating

Two digraphs on the same vertex type are equal if and only if their adjacency relations are logically equivalent.
-/

/-- Two digraphs on the same vertex type are equal if and only if their adjacency relations are logically equivalent. -/
theorem digraph_ext_iff {V : Type*} (D₁ D₂ : Digraph V) :
    D₁ = D₂ ↔ ∀ u v, D₁.Adj u v ↔ D₂.Adj u v := by
  constructor
  · intro h
    subst h
    simp
  · intro h
    cases D₁
    cases D₂
    simp only [Digraph.mk.injEq]
    funext u v
    exact propext (h u v)
