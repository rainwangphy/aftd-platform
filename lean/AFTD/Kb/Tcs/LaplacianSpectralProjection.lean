import AFTD.Prelude

/-!
# laplacian_spectral_projection

Topic: graphs   Node: 14725e911b7b

Provenance: formalization of a published result. Source: arXiv:2611.21567, Section 2

For a simple graph G and real number θ, the spectral projection E_θ of the Laplacian matrix L onto the eigenspace of θ is the sum of outer products of Laplacian orthonormal eigenvectors with eigenvalue θ.
-/

/-- Spectral projection matrix E_θ of the Laplacian matrix of G onto the eigenspace of θ. -/
noncomputable def laplacian_spectral_projection
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (θ : ℝ) :
    Matrix V V ℝ :=
  let hL := G.isHermitian_lapMatrix ℝ
  ∑ i : V, if hL.eigenvalues i = θ then
    Matrix.of (fun u v => (hL.eigenvectorBasis i u) * (hL.eigenvectorBasis i v))
  else 0
