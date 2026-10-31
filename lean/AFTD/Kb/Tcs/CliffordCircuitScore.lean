import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.PauliLabel
import AFTD.Kb.Tcs.PauliSize
import AFTD.Kb.Tcs.FullSupportPaulis
import AFTD.Kb.Tcs.ApplyCliffordCircuit

/-!
# clifford_circuit_score

Topic: quantum   Node: f6476cf649b2

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:370

The integer score S_k(U) of a k-qubit Clifford circuit circ : List (CliffordGate k), defined as the sum over all p in full_support_paulis k of 3^(k - pauli_size (apply_clifford_circuit circ p)).
-/

/-- The integer score S_k(U) of a k-qubit Clifford circuit. -/
def clifford_circuit_score {k : ℕ} (circ : List (CliffordGate k)) : ℕ := ∑ p ∈ full_support_paulis k, 3 ^ (k - pauli_size (apply_clifford_circuit circ p))
