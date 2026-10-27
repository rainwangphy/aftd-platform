import AFTD.Prelude

/-!
# simple_graph_adj_eigenvalues_sorted

Topic: graphs   Node: ee5fd075d889

Provenance: formalization of a published result. Source: arXiv:2610.18636 (spectral distances; nearest spectra to complete multipartite graphs): the adjacency eigenvalues lambda_1 >= ... >= lambda_n used in its spectral distances

For a type V with [Fintype V] and [DecidableEq V] (implicit V) and a simple graph G : SimpleGraph V, simple_graph_adj_eigenvalues_sorted G : Fin (Fintype.card V) → ℝ is defined, under `open scoped Classical` for the adjacency decidability, as `(G.isHermitian_adjMatrix ℝ).eigenvalues₀`: Matrix.IsHermitian.eigenvalues₀ of the Hermitian real adjacency matrix G.adjMatrix ℝ, with the ring ℝ passed explicitly to SimpleGraph.isHermitian_adjMatrix. These are the adjacency eigenvalues with multiplicity, listed in nonincreasing order (Mathlib proves Matrix.IsHermitian.eigenvalues₀_antitone).
-/

noncomputable def simple_graph_adj_eigenvalues_sorted {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Fin (Fintype.card V) → ℝ := open scoped Classical in (G.isHermitian_adjMatrix ℝ).eigenvalues₀
