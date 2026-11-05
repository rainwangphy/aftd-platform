import AFTD.Prelude

/-!
# adjacency_lambda2

Topic: graphs   Node: 645f904b486f

Provenance: formalization of a published result. Source: arXiv:2611.03879, Section 1

For any finite vertex type V and any simple graph G on V, the eigenvalue at index 1 of the real adjacency matrix (G.isHermitian_adjMatrix ℝ).eigenvalues₀ when 2 ≤ Fintype.card V (which is the second largest eigenvalue λ₂ of the adjacency matrix, as Mathlib's Matrix.IsHermitian.eigenvalues₀ is antitone: index 0 is the largest and index 1 is the second largest), defaulting to 0 if Fintype.card V < 2.
-/

/-- The second largest eigenvalue of the real adjacency matrix of a finite simple graph. -/
noncomputable def adjacency_lambda2 {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := open scoped Classical in
  if h : 2 ≤ Fintype.card V then
    (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨1, h⟩
  else 0
