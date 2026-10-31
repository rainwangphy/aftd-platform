import AFTD.Prelude

/-!
# CliffordGate

Topic: quantum   Node: d4f09efe7ca7

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:1610

An inductive type representing a quantum gate in a k-qubit Clifford circuit: Hadamard h on qubit i : Fin k, phase gate s on qubit i : Fin k, or controlled-NOT gate cnot with distinct control and target qubits c t : Fin k (with a proof c ≠ t).
-/

/-- A quantum gate in a k-qubit Clifford circuit: H on qubit i, S on qubit i, or CNOT with distinct control c and target t. -/
inductive CliffordGate (k : ℕ) where
  | h : Fin k → CliffordGate k
  | s : Fin k → CliffordGate k
  | cnot : (c t : Fin k) → c ≠ t → CliffordGate k
  deriving DecidableEq
