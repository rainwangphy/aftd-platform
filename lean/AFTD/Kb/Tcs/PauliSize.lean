import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLabel

/-!
# pauli_size

Topic: quantum   Node: 881ece1aa954

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:456

The weight (support size) of a k-qubit Pauli operator: the number of qubits on which the operator is not the identity.
-/

/-- The support size (Pauli weight) of a k-qubit Pauli label. -/
def pauli_size {k : ℕ} (p : PauliLabel k) : ℕ := Finset.card (Finset.filter (fun i => p.1 i ≠ 0 ∨ p.2 i ≠ 0) Finset.univ)
