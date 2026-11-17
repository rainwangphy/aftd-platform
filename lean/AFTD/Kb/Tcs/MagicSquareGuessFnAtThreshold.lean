import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareGuessFn
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0LtOne
import AFTD.Kb.Tcs.MagicSquareGuessFnLeOneOnIic
import AFTD.Kb.Tcs.MagicSquareGuessFnGeLinear

/-!
# magic_square_guess_fn_at_threshold

Topic: quantum   Node: 740b386c827d

Provenance: formalization of a published result. Source: arXiv:2610.12001 Cor. 5.2

At the threshold score $\beta_0 = \mathrm{magic\_square\_threshold\_beta0}$, the adversary's optimal guessing probability for Alice's complete first row in the magic square game is exactly 1: `magic_square_guess_fn magic_square_threshold_beta0 = 1`.
-/

/-- At the threshold score beta_0 = (2 + sqrt(2/3))/3, Alice's complete first row is perfectly predictable by an adversary with quantum side information: g(beta_0) = 1. -/
theorem magic_square_guess_fn_at_threshold : magic_square_guess_fn magic_square_threshold_beta0 = 1 := by
  apply le_antisymm (magic_square_guess_fn_le_one_on_Iic magic_square_threshold_beta0_lt_one.le)
  have h := magic_square_guess_fn_ge_linear 0 (le_refl _) (by linarith [magic_square_threshold_beta0_lt_one])
  simpa using h
