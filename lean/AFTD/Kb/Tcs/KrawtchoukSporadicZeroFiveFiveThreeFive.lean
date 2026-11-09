import AFTD.Prelude
import AFTD.Kb.Tcs.Krawtchouk

/-!
# krawtchouk_sporadic_zero_five_five_three_five

Topic: quantum   Node: 3cccc03d8358

Provenance: helper lemma. arXiv:2611.08518 Sec. 1

The binary Krawtchouk polynomial P_4^8 evaluated at 3 equals 0, verifying that the quadruple (m, n, k, ℓ) = (5, 5, 3, 5) satisfies the integral zero condition with m - 1 = 4 and k + ℓ = 8.
-/

/-- The binary Krawtchouk polynomial P_4^8 evaluated at 3 equals 0. -/
theorem krawtchouk_sporadic_zero_five_five_three_five : krawtchouk 8 4 3 = 0 := by
  unfold krawtchouk
  repeat rw [Finset.sum_range_succ]
  rw [Finset.sum_range_zero]
  norm_num [Nat.choose]
