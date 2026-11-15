import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactDigit

/-!
# op75_compact_digit_relu

Topic: np_completeness   Node: 23d2e2235c9b

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

The compact digit selector is the difference of the two rectified affine functions max(4x−1,0) and max(4x−2,0).
-/

lemma op75_compact_digit_relu (x : ℝ) :
    op75_compact_digit x = max (4*x-1) 0 - max (4*x-2) 0 := by
  unfold op75_compact_digit
  simp only [min_def, max_def]
  split_ifs <;> linarith
