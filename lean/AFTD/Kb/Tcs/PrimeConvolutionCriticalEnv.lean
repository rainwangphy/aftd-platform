import AFTD.Prelude
import AFTD.Kb.Tcs.TwoLevelPsi

/-!
# prime_convolution_critical_env

Topic: quantum   Node: 68c083f14163

Provenance: helper lemma. step towards prime_convolution_entanglement_breaking_iff_threshold

The critical (threshold) environment sigma_crit = |psi_p><psi_p| + sqrt(p(1-p)) * I on Fin d: the two-level pure environment shifted by sqrt(p(1-p)) times the identity. Its normalised Choi matrix is the matrix J(t) at the exact PPT threshold, J(1/(1+d sqrt(p(1-p)))) = (1/(1+d sqrt(p(1-p)))) * choi(sigma_crit).
-/

/-- Environment psi psi^T + sqrt (p (1 - p)) • 1 whose normalised Choi matrix is the critical (threshold) Choi matrix. -/
noncomputable def prime_convolution_critical_env (d : ℕ) (p : ℝ) : Matrix (Fin d) (Fin d) ℂ := Matrix.of (fun j l => (↑(two_level_psi d p j * two_level_psi d p l) : ℂ)) + (↑(Real.sqrt (p * (1 - p))) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
