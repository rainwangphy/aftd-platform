import AFTD.Prelude
import AFTD.Kb.Physics.VonNeumannEntropy
import AFTD.Kb.Tcs.IsQuantumState
import AFTD.Kb.Tcs.MatrixTraceLeft
import AFTD.Kb.Physics.FullyEntangledFraction

/-!
# two_qubit_min_bell_fidelity

Topic: quantum_mechanics   Node: 3d81b2b9cfa6

Provenance: formalization of a published result. Source: OP-1552; arXiv:2409.01966

For a real number ε, two_qubit_min_bell_fidelity ε is the real infimum sInf of the set of real numbers F such that there exists a complex matrix ρ on Fin 2 × Fin 2 satisfying is_quantum_state ρ, Real.log 2 + von_neumann_entropy ρ - von_neumann_entropy (Matrix.traceLeft ρ) ≤ ε, and F = fully_entangled_fraction ρ.
-/

/-- Minimum fully entangled fraction over two-qubit density matrices with adjusted entropy deficit at most epsilon. -/
noncomputable def two_qubit_min_bell_fidelity (ε : ℝ) : ℝ := sInf { F : ℝ | ∃ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
    is_quantum_state ρ ∧
    Real.log 2 + von_neumann_entropy ρ - von_neumann_entropy (Matrix.traceLeft ρ) ≤ ε ∧
    F = fully_entangled_fraction ρ }
