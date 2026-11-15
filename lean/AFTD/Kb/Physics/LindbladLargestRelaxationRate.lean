import AFTD.Prelude
import AFTD.Kb.Physics.LindbladDissipationSuperoperator

/-!
# lindblad_largest_relaxation_rate

Topic: quantum_mechanics   Node: 947f17f7d6a3

Provenance: formalization of a published result. Source: arXiv:2610.37187

The largest relaxation rate gamma in ℝ of the dissipation superoperator, defined as the supremum of the real parts of all complex eigenvalues in the spectrum over ℂ of lindblad_dissipation_superoperator J on Matrix (Fin d) (Fin d) ℂ.
-/

/-- The supremum of the real parts of the eigenvalues of the dissipation superoperator -L on Matrix (Fin d) (Fin d) ℂ. -/
noncomputable def lindblad_largest_relaxation_rate {ι : Type*} [Fintype ι] {d : ℕ}
    (J : ι → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sSup (Complex.re '' spectrum ℂ (lindblad_dissipation_superoperator J))
