import AFTD.Prelude
import AFTD.Kb.Tcs.BellNetworkLambda
import AFTD.Kb.Tcs.GhzCorrelationVector
import AFTD.Kb.Tcs.GhzNetworkLambdaStandardFrame

/-!
# ghz_two_copy_closed_lower_bound

Topic: quantum   Node: c92a3820aa93

Provenance: formalization of a published result. Source: arXiv:2610.35838 Corollary 1 (Eq. 15)

For every parameter alpha, there exist orthonormal frames e and f in O(3) and setting indices mu, nu, mu', nu' in {0, 1, 2, 3} such that the two-copy closed-network quantity Lambda(tau_{mu nu}, tau_{mu' nu'}) equals 1 + sin^2(2*alpha).
-/

/-- Analytical lower bound: there exist orthonormal frames attaining 1 + sin^2(2*alpha). -/
theorem ghz_two_copy_closed_lower_bound (α : ℝ) : ∃ (e f : Matrix (Fin 3) (Fin 3) ℝ), e ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧ f ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧ ∃ (μ ν μ' ν' : Fin 4), bell_network_lambda (ghz_correlation_vector α e f μ ν) (ghz_correlation_vector α e f μ' ν') = 1 + Real.sin (2 * α) ^ 2 := by
  use 1, 1
  refine ⟨Submonoid.one_mem _, Submonoid.one_mem _, ?_⟩
  use 3, 0, 1, 1
  exact ghz_network_lambda_standard_frame α
