import AFTD.Prelude

/-!
# digraph_is_isolated_edge

Topic: graphs   Node: f6a8baf6e2db

Provenance: formalization of a published result. Source: arXiv:2610.18600, Lemma 2.1

An edge uv in a digraph G is isolated if uv is an arc, u has no other out-neighbors and no in-neighbors, and v has no other in-neighbors and no out-neighbors.
-/

/-- An isolated edge in a digraph is an arc whose endpoints have no other incident arcs. -/
def digraph_is_isolated_edge {V : Type*} (G : Digraph V) (u v : V) : Prop := G.Adj u v ∧
  (∀ w, G.Adj u w → w = v) ∧
  (∀ w, ¬ G.Adj w u) ∧
  (∀ w, ¬ G.Adj v w) ∧
  (∀ w, G.Adj w v → w = u)
