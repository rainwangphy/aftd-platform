import AFTD.Prelude

/-!
# is_endpoint_cut_stable

Topic: algorithms   Node: 2f297f1affeb

Provenance: formalization of a published result. Source: arXiv:2610.23032 Section 8

A tree T on vertex type V is endpoint cut-stable with respect to metric d if for every edge {u, v} of T, deleting the edge leaves components with u and v such that d(u, v) ≤ d(u, x) for all x in the component of v and d(u, v) ≤ d(v, y) for all y in the component of u.
-/

/-- A spanning tree T on V is endpoint cut-stable with respect to d if deleting any edge uv leaves components A and B such that u is at least as close to v as to any other node in B and v is at least as close to u as to any other node in A. -/
def is_endpoint_cut_stable {V : Type*} (d : V → V → ℝ) (T : SimpleGraph V) : Prop := ∀ ⦃u v : V⦄, T.Adj u v →
    (∀ x, (T.deleteEdges {s(u, v)}).Reachable v x → d u v ≤ d u x) ∧
    (∀ y, (T.deleteEdges {s(u, v)}).Reachable u y → d u v ≤ d v y)
