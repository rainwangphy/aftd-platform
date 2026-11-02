import AFTD.Prelude

/-!
# is_orthonormal_hermitian_basis

Topic: quantum   Node: 87652ca6682b

Provenance: formalization of a published result. Source: arXiv:2610.36076 Sec. 6

The predicate asserting that a family T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ is an orthonormal Hermitian operator basis: every T a is Hermitian, every T a has trace zero, and for all a and b, the trace of T a * T b equals if a = b then 1 else 0.
-/

/-- A family T of d^2 - 1 matrices in Mat_d(C) is an orthonormal Hermitian operator basis if each T a is Hermitian, each has trace zero, and Tr(T a * T b) = delta_{ab}. -/
def is_orthonormal_hermitian_basis (d : ℕ) (T : Fin (d^2 - 1) → Matrix (Fin d) (Fin d) ℂ) : Prop := (∀ a, (T a).IsHermitian) ∧
  (∀ a, Matrix.trace (T a) = 0) ∧
  (∀ a b, Matrix.trace (T a * T b) = if a = b then 1 else 0)
