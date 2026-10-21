import AFTD.Prelude

/-!
# hn_eigenvalues

Topic: graphs   Node: d371cd1fd036

Provenance: formalization of a published result. Source: arXiv:2610.18636 Section 2

For a natural number n and real numbers l1, l2, l3, hn_eigenvalues n l1 l2 l3 is the function on Fin (3 * n) defined by: l1 at index 0, l2 at index 1, 0 at indices strictly between 1 and 3 * n - 2, l3 at index 3 * n - 2, and -(n : ℝ) elsewhere.
-/

/-- Eigenvalue sequence of H_n of length 3n in descending order. -/
def hn_eigenvalues (n : ℕ) (l1 l2 l3 : ℝ) : Fin (3 * n) → ℝ := fun i =>
  if i.val = 0 then l1
  else if i.val = 1 then l2
  else if i.val < 3 * n - 2 then 0
  else if i.val = 3 * n - 2 then l3
  else -(n : ℝ)
