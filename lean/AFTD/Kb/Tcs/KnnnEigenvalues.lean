import AFTD.Prelude

/-!
# knnn_eigenvalues

Topic: graphs   Node: cd6129025539

Provenance: formalization of a published result. Source: arXiv:2610.18636 Section 2

For a natural number n, knnn_eigenvalues n is the function on Fin (3 * n) defined by: 2 * (n : ℝ) at index 0, 0 at indices strictly between 0 and 3 * n - 2, and -(n : ℝ) at indices at least 3 * n - 2.
-/

/-- Eigenvalue sequence of K_{n,n,n} of length 3n in descending order. -/
def knnn_eigenvalues (n : ℕ) : Fin (3 * n) → ℝ := fun i =>
  if i.val = 0 then 2 * (n : ℝ)
  else if i.val < 3 * n - 2 then 0
  else -(n : ℝ)
