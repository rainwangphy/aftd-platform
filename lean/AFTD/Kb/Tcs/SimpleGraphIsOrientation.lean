import AFTD.Prelude

/-!
# simple_graph_is_orientation

Topic: graphs   Node: 8c024183cf43

Provenance: formalization of a published result. Source: scout/2610-09648-an-asymptotically-tight-bound-on-oriented-diameter.md:101

A digraph D is an orientation of a simple graph G if every directed edge of D is an edge of G and for every edge of G exactly one of the two directed edges is present in D.
-/

/-- A digraph D is an orientation of an undirected simple graph G if its edges are directed edges of G with exactly one direction chosen for each undirected edge of G. -/
def simple_graph_is_orientation {V : Type*} (D : Digraph V) (G : SimpleGraph V) : Prop := (∀ u v, D.Adj u v → G.Adj u v) ∧ ∀ u v, G.Adj u v → (D.Adj u v ↔ ¬ D.Adj v u)
