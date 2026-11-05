import AFTD.Prelude

/-!
# laplacian_mu1

Topic: graphs   Node: 8235eb085af3

Provenance: formalization of a published result. Source: arXiv:2611.03879, Section 1

For any finite vertex type V and any simple graph G on V, the largest eigenvalue μ₁ (Laplacian spectral radius) of the real Laplacian matrix L = D - A of G (indexed by 0 in nonincreasing order of eigenvalues), defaulting to 0 if V is empty.
-/

/-- The largest eigenvalue (spectral radius) of the real Laplacian matrix of a finite simple graph. -/
noncomputable def laplacian_mu1 {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := open scoped Classical in
  if h : 1 ≤ Fintype.card V then
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨0, h⟩
  else 0
