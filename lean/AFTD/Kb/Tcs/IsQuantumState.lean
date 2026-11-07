import AFTD.Prelude

/-!
# is_quantum_state

Topic: quantum   Node: 1728ac1877c9

Provenance: formalization of a published result. Source: arXiv:2610.34972 Section 1.3

A density matrix on a finite-dimensional Hilbert space is a positive semidefinite complex matrix with trace equal to 1.
-/

/-- A quantum state (density matrix) is a positive semidefinite complex matrix of trace one. -/
def is_quantum_state {d : Type*} [Fintype d] [DecidableEq d] (ρ : Matrix d d ℂ) : Prop := open ComplexOrder in ρ.PosSemidef ∧ ρ.trace = 1
