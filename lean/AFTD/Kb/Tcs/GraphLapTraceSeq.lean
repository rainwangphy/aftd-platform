import AFTD.Prelude

/-!
# graph_lap_trace_seq

Topic: graphs   Node: 286ac2d9e0db

Provenance: formalization of a published result. Source: arXiv:2610.36127 Definition 31

For a graph G on a finite vertex set V, its Laplacian trace sequence (ℓ_i(G))_{i=1}^∞ is the sequence of real numbers tr(L(G)^i) for positive integers i.
-/

/-- The Laplacian trace sequence of a graph, defined as the trace of powers L(G)^i for i ≥ 1. -/
noncomputable def graph_lap_trace_seq {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ+ → ℝ :=
  open scoped Classical in
  fun i ↦ ((G.lapMatrix ℝ) ^ (i : ℕ)).trace
