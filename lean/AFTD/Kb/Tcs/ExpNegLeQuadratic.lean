import AFTD.Prelude

/-!
# exp_neg_le_quadratic

Topic: learning   Node: 019ed21ba910

Provenance: helper lemma. TCSlib, `exp_neg_le_quadratic`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Quadratic upper bound on $e^{-t}$. For every real number $t \ge 0$, the value $e^{-t}$ is at most the second-order Taylor
polynomial $1 - t + t^2/2$; that is,
\[
  e^{-t} \;\le\; 1 - t + \frac{t^2}{2}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- For `t ≥ 0`, `exp(-t) ≤ 1 - t + t²/2` (the second-order upper Taylor bound for `exp(-t)`). Proof idea: multiply by `exp t > 0`; from the lower Taylor bound `1 + t + t²/2 ≤ exp t` we get `exp(t) (1 - t + t²/2) ≥ (1 + t + t²/2)(1 - t + t²/2) = 1 + t⁴/4 ≥ 1`. -/
lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  -- We prove the bound by multiplying both sides by `exp t > 0` and using the
  -- standard lower Taylor bound for `exp t`.
  have he : (0 : ℝ) < Real.exp t := exp_pos t
  have hq : (0 : ℝ) < 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg t]
  -- exp(t) ≥ 1 + t + t²/2
  have hquad := quadratic_le_exp_of_nonneg ht
  -- (1 + t + t²/2)(1 - t + t²/2) = 1 + t⁴/4 ≥ 1
  -- So exp(t) * (1 - t + t²/2) ≥ (1 + t + t²/2)(1 - t + t²/2) ≥ 1
  have key : 1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := by
    have : (1 + t + t ^ 2 / 2) * (1 - t + t ^ 2 / 2) = 1 + t ^ 4 / 4 := by ring
    nlinarith [sq_nonneg (t ^ 2), mul_le_mul_of_nonneg_right hquad hq.le]
  -- exp(-t) = (exp t)⁻¹ ≤ 1 - t + t²/2
  rw [exp_neg]
  exact le_of_mul_le_mul_left (by nlinarith [mul_inv_cancel₀ he.ne']) he
