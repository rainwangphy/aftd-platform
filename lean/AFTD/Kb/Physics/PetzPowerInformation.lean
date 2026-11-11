import AFTD.Prelude
import AFTD.Kb.Physics.PetzPowerDivergence
import AFTD.Kb.Tcs.MatrixTraceLeft
import AFTD.Kb.Tcs.MatrixTraceRight

/-!
# petz_power_information

Topic: quantum_mechanics   Node: cf653e31f56e

Provenance: formalization of a published result. Source: OP-1440

The Petz power mutual information petz_power_information β ρ of type ℝ for an exponent β : ℝ and a bipartite real matrix ρ : Matrix (u × v) (u × v) ℝ on finite types u, v with decidable equality, defined as petz_power_divergence β ρ (ρ.traceRight.kronecker ρ.traceLeft).
-/

/-- The Petz power mutual information I_beta(U : V)_rho. -/
noncomputable def petz_power_information {u v : Type*} [Fintype u] [Fintype v] [DecidableEq u] [DecidableEq v]
    (β : ℝ) (ρ : Matrix (u × v) (u × v) ℝ) : ℝ := petz_power_divergence β ρ (ρ.traceRight.kronecker ρ.traceLeft)
