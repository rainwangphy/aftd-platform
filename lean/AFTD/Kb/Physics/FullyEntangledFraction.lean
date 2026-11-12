import AFTD.Prelude
import AFTD.Kb.Physics.BellStateFidelity

/-!
# fully_entangled_fraction

Topic: quantum_mechanics   Node: 5dd9a62713f9

Provenance: formalization of a published result. Source: Bennett et al. 1996, Phys. Rev. A 54, 3824; OP-1552

The fully entangled fraction of a two-qubit density matrix ρ is the supremum over all 2-by-2 unitary matrices U of the fidelity of (I tensor U) ρ (I tensor U)* with the Bell state |Phi+>.
-/

/-- Fully entangled fraction of a two-qubit state, maximized over local unitaries on the second qubit. -/
noncomputable def fully_entangled_fraction (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := ⨆ U : Matrix.unitaryGroup (Fin 2) ℂ,
    bell_state_fidelity ((Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)) * ρ *
      star (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ)))
