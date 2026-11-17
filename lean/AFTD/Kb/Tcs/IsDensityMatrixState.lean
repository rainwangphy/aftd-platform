import AFTD.Prelude

/-!
# is_density_matrix_state

Topic: quantum   Node: 210b689dab27

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. II.3

A density matrix state on a finite-dimensional Hilbert space is an α × α complex matrix ρ whose associated linear map Matrix.toEuclideanLin ρ is positive semidefinite and whose matrix trace ρ.trace equals 1.
-/

/-- A quantum state is a positive semidefinite matrix with trace 1. -/
def is_density_matrix_state {α : Type*} [Fintype α] [DecidableEq α] (ρ : Matrix α α ℂ) : Prop := (Matrix.toEuclideanLin ρ).IsPositive ∧ ρ.trace = 1
