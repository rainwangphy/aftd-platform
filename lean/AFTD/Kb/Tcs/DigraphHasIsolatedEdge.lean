import AFTD.Prelude

/-!
# digraph_has_isolated_edge

Topic: graphs   Node: d8bda9a1f7d9

Provenance: formalization of a published result. Source: arXiv:2610.18600 Section 1.2

A digraph G on vertex type V has an isolated edge if there exist vertices u and v such that G has a directed edge from u to v, and every vertex w having a directed edge to or from u or v is equal to u or equal to v.
-/

/-- A digraph contains an isolated edge if some directed edge has no other incident edges. -/
def digraph_has_isolated_edge {V : Type*} (G : Digraph V) : Prop := ∃ u v : V, G.Adj u v ∧ ∀ w : V, (G.Adj u w ∨ G.Adj w u ∨ G.Adj v w ∨ G.Adj w v) → (w = u ∨ w = v)
