import AFTD.Prelude

/-!
# PauliLabel

Topic: quantum   Node: 6424c8cceffa

Provenance: formalization of a published result. Source: scout/2610-04621-exact-clifford-optimality-for-two-sided-locally-randomized.md:443

A binary symplectic Pauli label on k qubits, given as a pair of binary vectors (x, z) in (ZMod 2)^k x (ZMod 2)^k.
-/

/-- Binary symplectic Pauli coordinates (x, z) on k qubits. -/
abbrev PauliLabel (k : ℕ) : Type := (Fin k → ZMod 2) × (Fin k → ZMod 2)
