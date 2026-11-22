import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# three_mul_two_pow_add_one_gt_sq

Topic: combinatorics   Node: b179ab948030

Provenance: helper lemma. arXiv:2611.19312, Section 4, equation (1864)

For every integer r ≥ 3, 3 * (2^r + 1) is strictly greater than (r + 2)^2.
-/

/-- Exponential dominates quadratic bound for triangle Ramsey numbers: 3 * (2^r + 1) > (r + 2)^2. -/
theorem three_mul_two_pow_add_one_gt_sq (r : ℕ) (hr : 3 ≤ r) :
    (r + 2)^2 < 3 * (2^r + 1) := by
  induction' r, hr using Nat.le_induction with k hk ih
  · decide
  · have h1 : (k + 1 + 2)^2 + 3 ≤ 2 * (k + 2)^2 := by nlinarith
    have h2 : 2 * 2^k = 2^(k + 1) := by ring
    have h3 : 2 * (3 * (2^k + 1)) = 3 * (2^(k + 1) + 1) + 3 := by
      rw [← h2]
      ring
    omega
