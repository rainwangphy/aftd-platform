import AFTD.Prelude

/-!
# recurrence_matrix

Topic: combinatorics   Node: 3aafcd1d295d

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 2

For N : ℕ and a, b, c : Fin (N + 1) → ℝ, the tridiagonal matrix of size (N + 1) × (N + 1) has (i, j) entry equal to a i when j.val = i.val + 1, b i when j.val = i.val, c i when i.val = j.val + 1, and 0 otherwise.
-/

/-- Tridiagonal recurrence matrix J on Fin (N + 1). -/
noncomputable def recurrence_matrix (N : ℕ) (a b c : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun i j =>
    if j.val = i.val + 1 then a i
    else if j.val = i.val then b i
    else if i.val = j.val + 1 then c i
    else 0
