import AFTD.Prelude

/-!
# graph_interval_index

Topic: graphs   Node: f7343913bb42

Provenance: formalization of a published result. Source: arXiv:2610.39966 Section 1

The interval index of a finite graph G is the sum over all 2-element subsets {u, v} of vertices of |I(u, v)| - 1, where I(u, v) is the interval between u and v consisting of all vertices w with d(u, w) + d(w, v) = d(u, v).
-/

open scoped Classical in
/-- The interval index Int(G) of a finite graph G. -/
noncomputable def graph_interval_index {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := ∑ uv ∈ (Finset.univ : Finset (Finset V)).filter (·.card = 2),
    ((Finset.univ.filter (fun w => ∀ u ∈ uv, ∀ v ∈ uv, u ≠ v → G.dist u w + G.dist w v = G.dist u v)).card - 1)
