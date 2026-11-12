import AFTD.Prelude

/-!
# binary_entropy_nats

Topic: quantum_mechanics   Node: d7134ec0a3b1

Provenance: formalization of a published result. Source: Nielsen & Chuang, Quantum Computation and Quantum Information, Section 11.2

The binary entropy function in natural units (nats) is -x ln x - (1 - x) ln (1 - x) with the convention 0 ln 0 = 0.
-/

/-- Binary Shannon entropy in natural units (nats) with the convention 0 ln 0 = 0. -/
noncomputable def binary_entropy_nats (x : ℝ) : ℝ := Real.negMulLog x + Real.negMulLog (1 - x)
