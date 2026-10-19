import AFTD.Prelude

/-!
# adjacency_spectral_radius

Topic: graphs   Node: cf1b1685ce5c

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 2

The adjacency spectral radius of a simple graph G on a finite vertex set is the spectral radius of its real adjacency matrix.
-/

/-- The adjacency spectral radius of a simple graph on a finite vertex set. -/
noncomputable def adjacency_spectral_radius {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ENNReal := open scoped Classical in spectralRadius ℝ (G.adjMatrix ℝ)
