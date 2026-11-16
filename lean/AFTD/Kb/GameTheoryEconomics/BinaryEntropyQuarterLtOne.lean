import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryEntropy

/-!
# binaryEntropy_quarter_lt_one

Topic: equilibria   Node: d4e990ab2465

Provenance: helper lemma. arXiv:2611.18470, Appendix D.1

The binary entropy of 1/4 is strictly less than 1.
-/

/-- The binary entropy at 1/4 is strictly less than 1. -/
theorem binaryEntropy_quarter_lt_one : binaryEntropy (1 / 4) < 1 := by
  have hform (z : ℝ) : binaryEntropy z = Real.binEntropy z / Real.log 2 := by
    simp only [binaryEntropy, Real.binEntropy, Real.logb, Real.log_inv]
    ring
  rw [hform]
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_one hp]
  rw [Real.binEntropy_lt_log_two]
  norm_num
