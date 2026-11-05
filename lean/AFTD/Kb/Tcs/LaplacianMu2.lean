import AFTD.Prelude

/-!
# laplacian_mu2

Topic: graphs   Node: 7dd9972f5b48

Provenance: formalization of a published result. Source: arXiv:2611.03879, Section 1

For any finite vertex type V and any simple graph G on V, the second largest eigenvalue μ₂ of the real Laplacian matrix L = D - A of G, defined using Mathlib's antitone eigenvalue sequence Matrix.IsHermitian.eigenvalues₀ (where eigenvalues₀_antitone guarantees nonincreasing order): if 2 ≤ Fintype.card V (with proof h), it is (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨1, h⟩, and 0 otherwise.
-/

/-- The second largest eigenvalue of the real Laplacian matrix of a finite simple graph. -/
noncomputable def laplacian_mu2 {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := open scoped Classical in
  if h : 2 ≤ Fintype.card V then
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨1, h⟩
  else 0
