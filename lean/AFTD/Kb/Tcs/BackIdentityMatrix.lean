import AFTD.Prelude

/-!
# back_identity_matrix

Topic: combinatorics   Node: 24d9f484aed0

Provenance: formalization of a published result. Source: arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), Theorem 3 and Theorem 5: the matrix R of the Goethals-Seidel array

The back-identity (reversal) matrix R of order m over ℤ: R i j = 1 when i + j ≡ m - 1 (mod m), equivalently i + j + 1 = m for indices below m, and 0 otherwise.
-/

/-- The back-identity (reversal) matrix R of order m over ℤ: R i j = 1 when i + j ≡ m - 1 (mod m), equivalently i + j + 1 = m for indices below m, and 0 otherwise. -/
def back_identity_matrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => if (i : ℕ) + j + 1 = m then 1 else 0
