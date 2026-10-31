import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLabel
import AFTD.Kb.Tcs.PauliSize

/-!
# full_support_paulis

Topic: quantum   Node: 365baa12e624

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:368

The set of full-support Pauli operators on k qubits, acting non-trivially on every qubit.
-/

/-- The finset of full-support Pauli operators on k qubits. -/
def full_support_paulis (k : ℕ) : Finset (PauliLabel k) := Finset.filter (fun p => pauli_size p = k) Finset.univ
