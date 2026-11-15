import AFTD.Prelude

/-!
# hermitian_lindblad_jump_weight

Topic: quantum_mechanics   Node: c97fec993182

Provenance: formalization of a published result. Source: arXiv:2610.37187

The total jump weight W in ℝ of a family of d-by-d complex matrices J : ι → Matrix (Fin d) (Fin d) ℂ, defined as the sum over all j in ι of the real part of the trace of J j * J j.
-/

/-- The total jump weight W in ℝ, defined as the sum over j of the real part of Tr((J j) * (J j)). -/
noncomputable def hermitian_lindblad_jump_weight {ι : Type*} [Fintype ι] {d : ℕ}
    (J : ι → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ j, (Matrix.trace (J j * J j)).re
