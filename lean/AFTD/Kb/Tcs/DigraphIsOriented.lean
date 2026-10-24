import AFTD.Prelude

/-!
# digraph_is_oriented

Topic: graphs   Node: f1a94975e276

Provenance: formalization of a published result. Source: arXiv:2610.18600 Section 1

A digraph G : Digraph V on vertex type V is oriented (digraph_is_oriented G) if for all vertices u v : V, G.Adj u v implies ¬ G.Adj v u.
-/

/-- A digraph G is oriented if it contains no directed 2-cycles and no loops. -/
def digraph_is_oriented {V : Type*} (G : Digraph V) : Prop := ∀ u v, G.Adj u v → ¬ G.Adj v u
