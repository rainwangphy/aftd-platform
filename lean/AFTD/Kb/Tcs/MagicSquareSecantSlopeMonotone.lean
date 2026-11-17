import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareGuessFn
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0
import AFTD.Kb.Tcs.MagicSquareGuessFnConcaveOn
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0LtOne
import AFTD.Kb.Tcs.MagicSquareGuessFnAtThreshold

/-!
# magic_square_secant_slope_monotone

Topic: quantum   Node: ee8646b64356

Provenance: helper lemma. arXiv:2610.12001 Sec. 6

For any real numbers $\delta_1, \delta_2$ satisfying $0 < \delta_1 \le \delta_2 \le 1 - \beta_0$, where $\beta_0 = \mathrm{magic\_square\_threshold\_beta0}$ and $g = \mathrm{magic\_square\_guess\_fn}$, the secant slope of the predictability loss $(1 - g(\beta_0 + \delta)) / \delta$ is non-decreasing in $\delta$: $(1 - g(\beta_0 + \delta_1)) / \delta_1 \le (1 - g(\beta_0 + \delta_2)) / \delta_2$.
-/

/-- The difference quotient (1 - g(beta_0 + delta)) / delta of predictability loss is non-decreasing in delta on (0, 1 - beta_0]. -/
theorem magic_square_secant_slope_monotone (δ₁ δ₂ : ℝ)
    (h1 : 0 < δ₁) (h12 : δ₁ ≤ δ₂) (h2 : δ₂ ≤ 1 - magic_square_threshold_beta0) :
    (1 - magic_square_guess_fn (magic_square_threshold_beta0 + δ₁)) / δ₁ ≤
      (1 - magic_square_guess_fn (magic_square_threshold_beta0 + δ₂)) / δ₂ := by
  have h := (magic_square_guess_fn_concaveOn.neg).secant_mono
    (a := magic_square_threshold_beta0)
    (x := magic_square_threshold_beta0 + δ₁)
    (y := magic_square_threshold_beta0 + δ₂)
    (by simp; exact magic_square_threshold_beta0_lt_one.le)
    (by simp; linarith)
    (by simp; linarith)
    (by linarith) (by linarith) (by linarith)
  simpa [magic_square_guess_fn_at_threshold, sub_eq_add_neg, add_comm] using h
