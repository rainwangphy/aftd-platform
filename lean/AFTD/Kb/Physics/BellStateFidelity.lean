import AFTD.Prelude

/-!
# bell_state_fidelity

Topic: quantum_mechanics   Node: 308da49ec44c

Provenance: formalization of a published result. Source: Nielsen & Chuang, Quantum Computation and Quantum Information, Section 1.3

The fidelity of a two-qubit operator M with the standard Bell state |Phi+> is the real part of (M_{(0,0),(0,0)} + M_{(0,0),(1,1)} + M_{(1,1),(0,0)} + M_{(1,1),(1,1)}) / 2.
-/

/-- Fidelity of a two-qubit state with the maximally entangled Bell state |Phi+> = (|00> + |11>) / sqrt(2). -/
noncomputable def bell_state_fidelity (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := (M (0, 0) (0, 0) + M (0, 0) (1, 1) + M (1, 1) (0, 0) + M (1, 1) (1, 1)).re / 2
