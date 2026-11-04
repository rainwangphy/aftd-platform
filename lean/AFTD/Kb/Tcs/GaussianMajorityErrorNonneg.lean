import AFTD.Prelude
import AFTD.Kb.Tcs.GaussianMajorityError

/-!
# gaussian_majority_error_nonneg

Topic: communication   Node: 9896d4b05888

Provenance: helper lemma. arXiv:2610.16830, target: gaussian_coin_majority_worst_variance_zeta_crossover

For any natural number q and any real lam > 0, the error 0 ≤ gaussian_majority_error q lam.
-/

/-- The Gaussian majority communication error is always nonnegative. -/
theorem gaussian_majority_error_nonneg (q : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ gaussian_majority_error q lam := by
  unfold gaussian_majority_error
  refine Real.le_iInf (fun _ => ?_) le_rfl
  refine Real.le_iInf (fun _ => ?_) le_rfl
  refine Real.le_iInf (fun _ => ?_) le_rfl
  refine Real.le_iInf (fun _ => ?_) le_rfl
  exact ENNReal.toReal_nonneg
