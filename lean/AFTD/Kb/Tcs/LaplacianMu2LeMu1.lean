import AFTD.Prelude
import AFTD.Kb.Tcs.LaplacianMu1
import AFTD.Kb.Tcs.LaplacianMu2

/-!
# laplacian_mu2_le_mu1

Topic: graphs   Node: 6eec7dfd0ac9

Provenance: helper lemma. folklore

For any finite vertex type V and any simple graph G on V with at least 2 vertices (2 ≤ Fintype.card V), the second largest Laplacian eigenvalue is at most the largest Laplacian eigenvalue: laplacian_mu2 G ≤ laplacian_mu1 G.
-/

/-- The second largest Laplacian eigenvalue is at most the largest Laplacian eigenvalue. -/
theorem laplacian_mu2_le_mu1 {V : Type*} [Fintype V] (G : SimpleGraph V) (hV : 2 ≤ Fintype.card V) :
    laplacian_mu2 G ≤ laplacian_mu1 G := by
  classical
  dsimp [laplacian_mu2, laplacian_mu1]
  have h1 : 1 ≤ Fintype.card V := by omega
  rw [dif_pos hV, dif_pos h1]
  apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
  exact Nat.zero_le 1
