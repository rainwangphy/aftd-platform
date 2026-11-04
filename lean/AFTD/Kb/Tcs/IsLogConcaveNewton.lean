import AFTD.Prelude
import AFTD.Kb.Tcs.NewtonCoeff

/-!
# is_log_concave_newton

Topic: combinatorics   Node: 4580d1aeb47b

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 3

For N : ℕ and d : Fin (N + 1) → ℝ, the profile has log-concave Newton coefficients if newton_coeff N d k ≥ 0 for all 1 ≤ k ≤ N and (newton_coeff N d k)^2 ≥ newton_coeff N d (k - 1) * newton_coeff N d (k + 1) for all 2 ≤ k < N.
-/

/-- A profile has log-concave Newton coefficients without internal zeros. -/
def is_log_concave_newton (N : ℕ) (d : Fin (N + 1) → ℝ) : Prop := (∀ k ∈ Finset.Icc 1 N, 0 ≤ newton_coeff N d k) ∧
  (∀ k ∈ Finset.Ico 2 N, (newton_coeff N d k) ^ 2 ≥ newton_coeff N d (k - 1) * newton_coeff N d (k + 1))
