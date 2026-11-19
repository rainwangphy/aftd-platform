import AFTD.Prelude
import AFTD.Kb.Tcs.LaplacianSpectralProjection

/-!
# laplacian_mutual_eigenvalue_support

Topic: graphs   Node: 88854945e408

Provenance: formalization of a published result. Source: arXiv:2611.21567, Section 2

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and two vertices u, v : V, laplacian_mutual_eigenvalue_support G u v is the finite set (Finset ℝ) of all eigenvalues θ of the real Laplacian matrix of G such that the (u, v)-entry of laplacian_spectral_projection G θ is nonzero.
-/

/-- The mutual eigenvalue support ev_L(u,v) of vertices u, v in G. -/
noncomputable def laplacian_mutual_eigenvalue_support
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    Finset ℝ :=
  let hL := G.isHermitian_lapMatrix ℝ
  Finset.filter (fun θ => laplacian_spectral_projection G θ u v ≠ 0)
    (Finset.image hL.eigenvalues Finset.univ)
