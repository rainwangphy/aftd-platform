import AFTD.Prelude

/-!
# graph_adj_trace_seq

Topic: graphs   Node: 4009fc392f2f

Provenance: formalization of a published result. Source: arXiv:2610.36127 Definition 13

For a graph G on a finite vertex set V, its adjacency trace sequence (a_i(G))_{i=1}^∞ is the sequence of real numbers tr(A(G)^i) for positive integers i.
-/

/-- The adjacency trace sequence of a graph, defined as the trace of powers A(G)^i for i ≥ 1. -/
noncomputable def graph_adj_trace_seq {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ+ → ℝ :=
  open scoped Classical in
  fun i ↦ ((G.adjMatrix ℝ) ^ (i : ℕ)).trace
