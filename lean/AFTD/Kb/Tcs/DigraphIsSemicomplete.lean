import AFTD.Prelude

/-!
# digraph_is_semicomplete

Topic: graphs   Node: 90154757bfbd

Provenance: formalization of a published result. Source: arXiv:2610.36895 Sec. 1

A digraph D is semicomplete if it is loopless and for every pair of distinct vertices u and v, at least one directed edge exists between them (u → v or v → u).
-/

/-- A digraph is semicomplete if it is loopless and has at least one arc between every distinct pair of vertices. -/
def digraph_is_semicomplete {V : Type*} (D : Digraph V) : Prop := (∀ v : V, ¬ D.Adj v v) ∧ ∀ u v : V, u ≠ v → D.Adj u v ∨ D.Adj v u
