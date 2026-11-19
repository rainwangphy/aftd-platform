import AFTD.Prelude
import AFTD.Kb.Tcs.BapatSunderMatrix

/-!
# is_real_bapat_sunder_counterexample

Topic: combinatorics   Node: 2b78c7616605

Provenance: formalization of a published result. Source: arXiv:2611.23269, Theorem 1 and Section 1

A real square matrix A of size (n+1) x (n+1) is a positive semidefinite counterexample to the Bapat-Sunder eigenvalue conjecture if A is positive semidefinite and there exists a vector x : Fin (n + 1) → ℝ such that dotProduct x (Matrix.mulVec (bapat_sunder_matrix A) x) > A.permanent * dotProduct x x.
-/

/-- Predicate asserting that a real matrix is a positive semidefinite counterexample to the Bapat-Sunder eigenvalue conjecture. -/
def is_real_bapat_sunder_counterexample {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop := A.PosSemidef ∧ ∃ x : Fin (n + 1) → ℝ,
    dotProduct x (Matrix.mulVec (bapat_sunder_matrix A) x) > A.permanent * dotProduct x x
