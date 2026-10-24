import AFTD.Prelude
import AFTD.Kb.Tcs.AdjacencySpectralRadius

/-!
# is_perron_vector

Topic: graphs   Node: dc3febee6cac

Provenance: formalization of a published result. Source: arXiv:2610.17078, Section 2

For a simple graph G on a finite vertex type V, a vector vec : V → ℝ is a Perron vector if every component vec i is strictly positive and vec is an eigenvector of the real adjacency matrix of G with eigenvalue equal to the real value of the adjacency spectral radius of G.
-/

/-- A Perron vector of a simple graph is a strictly positive eigenvector of its adjacency matrix with eigenvalue equal to its spectral radius. -/
noncomputable def is_perron_vector {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (vec : V → ℝ) : Prop := open scoped Classical in
  (∀ i, 0 < vec i) ∧ (G.adjMatrix ℝ).mulVec vec = (ENNReal.toReal (adjacency_spectral_radius G)) • vec
