import AFTD.Prelude

/-!
# is_quantum_effect

Topic: quantum   Node: 24601e315b98

Provenance: formalization of a published result. Source: arXiv:2610.37347 Sec. 'Steering and incompatibility preservation'

A matrix M on C^d is a quantum effect if both M and I - M are positive semidefinite.
-/

/-- A quantum effect (binary measurement element) on C^d: a positive semidefinite matrix M such that I - M is also positive semidefinite. -/
def is_quantum_effect {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : Prop := open scoped ComplexOrder in M.PosSemidef ∧ (1 - M).PosSemidef
