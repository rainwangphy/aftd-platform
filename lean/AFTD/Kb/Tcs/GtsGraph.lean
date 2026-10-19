import AFTD.Prelude

/-!
# gts_graph

Topic: graphs   Node: 356f97869391

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 2

The graph obtained from T by deleting all edges between candidate v and its neighbours other than w, and inserting edges between beneficiary u and those neighbours.
-/

/-- The graph formed by removing all edges between v and N(v) \ {w} and adding edges between u and N(v) \ {w}. -/
def gts_graph {V : Type*} (T : SimpleGraph V) (u v w : V) : SimpleGraph V := T.deleteEdges { e | ∃ z, e = s(v, z) ∧ T.Adj v z ∧ z ≠ w } ⊔
    SimpleGraph.fromEdgeSet { e | ∃ z, e = s(u, z) ∧ T.Adj v z ∧ z ≠ w }
