import AFTD.Prelude

/-!
# goethals_seidel_array

Topic: combinatorics   Node: b097f4a2908f

Provenance: formalization of a published result. Source: arXiv:2610.27175 (Recent progress in the construction of Hadamard matrices), Theorem 3 (the Goethals-Seidel array)

The Goethals-Seidel array of order 4m in four m × m matrices A, B, C, D and R, indexed by (block row, row): rows of blocks (A, BR, CR, DR), (-BR, A, DᵀR, -CᵀR), (-CR, -DᵀR, A, BᵀR), (-DR, CᵀR, -BᵀR, A).
-/

/-- The Goethals-Seidel array of order 4m in four m × m matrices A, B, C, D and R, indexed by (block row, row): rows of blocks (A, BR, CR, DR), (-BR, A, DᵀR, -CᵀR), (-CR, -DᵀR, A, BᵀR), (-DR, CᵀR, -BᵀR, A). -/
def goethals_seidel_array {m : ℕ} (A B C D R : Matrix (Fin m) (Fin m) ℤ) :
    Matrix (Fin 4 × Fin m) (Fin 4 × Fin m) ℤ :=
  Matrix.of fun p q =>
    (![![A, B * R, C * R, D * R],
       ![-(B * R), A, D.transpose * R, -(C.transpose * R)],
       ![-(C * R), -(D.transpose * R), A, B.transpose * R],
       ![-(D * R), C.transpose * R, -(B.transpose * R), A]] p.1 q.1) p.2 q.2
