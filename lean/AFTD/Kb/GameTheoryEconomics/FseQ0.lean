import AFTD.Prelude

/-!
# fse_q0

Topic: mechanism_design   Node: c441760f481e

The linear scaling function q(y) = 1 - 9y/10.
-/

/-- The linear scaling function `q(y) = 1 - 9y/10`. -/
noncomputable def fse_q0 (y : ℝ) : ℝ := 1 - 9 / 10 * y
