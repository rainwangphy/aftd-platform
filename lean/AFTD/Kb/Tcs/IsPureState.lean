import AFTD.Prelude

/-!
# is_pure_state

Topic: quantum   Node: 0f2eac279d5c

Provenance: formalization of a published result. Source: arXiv:2610.36076 Sec. 2

A matrix rho on C^d represents a pure quantum state if and only if rho is Hermitian, idempotent (rho^2 = rho), and has trace 1.
-/

/-- A density matrix rho on C^d represents a pure quantum state if and only if it is Hermitian, idempotent (a projector), and has unit trace. -/
def is_pure_state {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop := ρ.IsHermitian ∧ ρ * ρ = ρ ∧ Matrix.trace ρ = 1
