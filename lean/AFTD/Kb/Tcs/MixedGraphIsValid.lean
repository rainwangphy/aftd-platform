import AFTD.Prelude

/-!
# mixed_graph_is_valid

Topic: graphs   Node: ed4d21fe02d0

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Sec. 2 (mixed graphs: edges and arcs, no loops, at most one edge or arc between two vertices).

A mixed graph on V: undirected edges E (a simple graph) and arcs A, with no loops and at most one edge or arc between two vertices (no antiparallel arcs, no arc parallel to an edge).
-/

/-- `(E, A)` is a mixed graph: `A` is irreflexive and asymmetric (no antiparallel arcs) and no arc joins two vertices joined by an edge. `E` is a `SimpleGraph`, so it has no loops or parallel edges. -/
def mixed_graph_is_valid {V : Type*} (E : SimpleGraph V) (A : V → V → Prop) : Prop :=
  (∀ x, ¬ A x x) ∧ (∀ x y, A x y → ¬ A y x) ∧ ∀ x y, E.Adj x y → ¬ A x y
