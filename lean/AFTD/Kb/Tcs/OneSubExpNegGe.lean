import AFTD.Prelude
import AFTD.Kb.Tcs.ExpNegLeQuadratic

/-!
# one_sub_exp_neg_ge

Topic: learning   Node: a60abbd823ad

Provenance: helper lemma. TCSlib, `one_sub_exp_neg_ge`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lower bound on $1 - e^{-\eta}$. For every real number $\eta > 0$, the quantity $1 - e^{-\eta}$ is bounded below by its
second-order Taylor expansion at the origin:
\[
  1 - e^{-\eta} \;\ge\; \eta - \frac{\eta^{2}}{2}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- For `η > 0`, `1 - exp(-η) ≥ η - η²/2`: the rearranged form of `exp_neg_le_quadratic`. This is the relaxation of the chord coefficient `1 - e^{-η}` that turns the per-step bound `log_potential_step` into `-η · hedgeLoss + η²/2` in the weak regret bound. -/
lemma one_sub_exp_neg_ge {η : ℝ} (hη : 0 < η) :
    1 - Real.exp (-η) ≥ η - η ^ 2 / 2 := by
  -- Rearranged form of the previous quadratic upper bound on `exp (-η)`.
  have h := exp_neg_le_quadratic hη.le
  linarith
