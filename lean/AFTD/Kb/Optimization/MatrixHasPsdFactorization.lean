import AFTD.Prelude

/-!
# matrix_has_psd_factorization

Topic: integer_programming   Node: 78ec3e181404

Provenance: formalization of a published result. Source: scout/2610-04498-rank-sensitive-vertex-bounds-for-semidefinite-lifts.md:351

For types m and n, a real matrix M : Matrix m n ℝ has a positive semidefinite (PSD) factorization of size r (for a natural number r) if there exist families of r × r positive semidefinite matrices A : m → Matrix (Fin r) (Fin r) ℝ and B : n → Matrix (Fin r) (Fin r) ℝ such that each A i and B j is positive semidefinite and M i j = Matrix.trace (A i * B j) for all i and j.
-/

/-- A real matrix has a positive semidefinite factorization of size r if its entries can be written as traces of products of r × r positive semidefinite matrices. -/
def matrix_has_psd_factorization {m n : Type*} (M : Matrix m n ℝ) (r : ℕ) : Prop := ∃ (A : m → Matrix (Fin r) (Fin r) ℝ) (B : n → Matrix (Fin r) (Fin r) ℝ),
    (∀ i, (A i).PosSemidef) ∧ (∀ j, (B j).PosSemidef) ∧ ∀ i j, M i j = Matrix.trace (A i * B j)
