import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquarePredictabilitySlopeOfLowerBound
import AFTD.Kb.Tcs.MagicSquareGuessFnLeOneOnIic
import AFTD.Kb.Tcs.MagicSquareGuessFn
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0

/-!
# magic_square_predictability_loss_slope_exists

Topic: quantum   Node: 75d9bcd28398

Provenance: helper lemma. arXiv:2610.12001, Section 6 and Corollary 6.2; analysis of the right-hand secant limit.

The predictability-loss right-hand slope exists and lies between zero and the established upper bound.
-/

theorem magic_square_predictability_loss_slope_exists : ∃ c : ℝ, 0 ≤ c ∧ c ≤ 3 / (4 * (1 - magic_square_threshold_beta0)) ∧ Filter.Tendsto (fun δ : ℝ => (1 - magic_square_guess_fn (magic_square_threshold_beta0 + δ)) / δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  apply magic_square_predictability_slope_of_lower_bound 0
  intro δ hδ hδR
  have h := magic_square_guess_fn_le_one_on_Iic (w := magic_square_threshold_beta0 + δ) (by linarith)
  linarith
