import AFTD.Prelude

/-!
# LinIneq

Topic: proof_complexity   Node: c0590d1d25d5

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 4.1

A linear inequality c^T x ≥ d over n Boolean variables, with integer coefficient vector c : Fin n → ℤ and integer constant term d : ℤ.
-/

/-- A linear inequality c^T x ≥ d over n Boolean variables, with integer coefficients and constant. -/
structure LinIneq (n : ℕ) where
  coeffs : Fin n → ℤ
  const : ℤ
