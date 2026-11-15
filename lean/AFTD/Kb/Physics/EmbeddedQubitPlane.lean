import AFTD.Prelude

/-!
# EmbeddedQubitPlane

Topic: quantum_mechanics   Node: b4839a8a8ebe

Provenance: original. Related work: arXiv:2610.37187

An embedded qubit plane in dimension d consists of a rank-two orthogonal projector P and an orthonormal pair E1, E2 of traceless Hermitian matrices supported on P.
-/

/-- An orthonormal frame for a two-dimensional real subspace of traceless Hermitian matrices supported on a rank-two projector. -/
structure EmbeddedQubitPlane (d : ℕ) where
  P : Matrix (Fin d) (Fin d) ℂ
  E₁ : Matrix (Fin d) (Fin d) ℂ
  E₂ : Matrix (Fin d) (Fin d) ℂ
  hP_herm : P.IsHermitian
  hP_proj : P * P = P
  hP_trace : P.trace = 2
  hE₁_herm : E₁.IsHermitian
  hE₂_herm : E₂.IsHermitian
  hE₁_supp : P * E₁ * P = E₁
  hE₂_supp : P * E₂ * P = E₂
  hE₁_trace : E₁.trace = 0
  hE₂_trace : E₂.trace = 0
  hE₁_norm : (Matrix.trace (E₁ * E₁)).re = 1
  hE₂_norm : (Matrix.trace (E₂ * E₂)).re = 1
  hE_ortho : (Matrix.trace (E₁ * E₂)).re = 0
