import AFTD.Prelude

/-!
# is_graph_orientation

Topic: graphs   Node: a69b7a4c455e

Provenance: formalization of a published result. Source: arXiv:2610.09648 Section 1

A digraph D is an orientation of a simple graph G if every edge of G is assigned exactly one direction in D, and non-adjacent pairs in G are not adjacent in D.
-/

/-- A digraph D is an orientation of a simple graph G. -/
def is_graph_orientation {V : Type*} (G : SimpleGraph V) (D : Digraph V) : Prop := (∀ u v, D.Adj u v ∨ D.Adj v u ↔ G.Adj u v) ∧ ∀ u v, ¬(D.Adj u v ∧ D.Adj v u)
