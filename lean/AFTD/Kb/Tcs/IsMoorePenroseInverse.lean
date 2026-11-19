import AFTD.Prelude

/-!
# is_moore_penrose_inverse

Topic: graphs   Node: 672c45be4359

Provenance: formalization of a published result. Source: Penrose 1955, A generalized inverse for matrices, Proc. Cambridge Philos. Soc. 51:406-413

A real matrix A_pinv is the Moore-Penrose pseudoinverse of A if A * A_pinv * A = A, A_pinv * A * A_pinv = A_pinv, and both A * A_pinv and A_pinv * A are symmetric.
-/

/-- A real matrix A_pinv is the Moore-Penrose pseudoinverse of A. -/
def is_moore_penrose_inverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (A_pinv : Matrix n m ℝ) : Prop :=
  A * A_pinv * A = A ∧
  A_pinv * A * A_pinv = A_pinv ∧
  Matrix.transpose (A * A_pinv) = A * A_pinv ∧
  Matrix.transpose (A_pinv * A) = A_pinv * A
