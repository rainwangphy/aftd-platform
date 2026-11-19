import AFTD.Prelude
import AFTD.Kb.Tcs.LaplacianSpectralProjection

/-!
# laplacian_bounding_entry

Topic: graphs   Node: a27af6ca1316

Provenance: formalization of a published result. Source: arXiv:2611.21567, Section 2

For a finite simple graph $G$ and vertices $u, v$, the Laplacian bounding entry $(B_L)_{u,v}$ is defined as the sum over all distinct Laplacian eigenvalues $\theta$ of the absolute value of the $(u,v)$-entry of the spectral projection $E_\theta$.
-/

/-- The (u,v)-entry of the bounding matrix B_L for Laplacian peak state transfer. -/
noncomputable def laplacian_bounding_entry
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℝ :=
  let hL := G.isHermitian_lapMatrix ℝ
  ∑ θ ∈ Finset.image hL.eigenvalues Finset.univ, |laplacian_spectral_projection G θ u v|
