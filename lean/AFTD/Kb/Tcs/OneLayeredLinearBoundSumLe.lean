import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# one_layered_linear_bound_sum_le

Topic: combinatorics   Node: f54b1e7c2c36

Provenance: helper lemma. arXiv:2611.08071 Theorem 2.1

For integers r ≥ 2, k ≥ 1, r ≤ m, and S with k * r ≤ S ≤ 2 * m - r, the block sum 2^(r - 2) * (S - k * r) + k is at most 2^(r - 1) * (m - r) + 1.
-/

/-- Summation arithmetic bound for the block decomposition in Theorem 2.1. -/
theorem one_layered_linear_bound_sum_le (m r k S : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hm : r ≤ m)
    (hS : S ≤ 2 * m - r) (hkr : k * r ≤ S) :
    2 ^ (r - 2) * (S - k * r) + k ≤ 2 ^ (r - 1) * (m - r) + 1 := by
  have hr1 : r - 1 = (r - 2) + 1 := by omega
  have hpow : 2 ^ (r - 1) = 2 ^ (r - 2) * 2 := by
    rw [hr1, pow_succ, mul_comm]
  rw [hpow]
  zify [hkr, hm]
  set P : ℤ := (2 : ℤ) ^ (r - 2)
  change P * (↑S - ↑k * ↑r) + ↑k ≤ P * 2 * (↑m - ↑r) + 1
  have hP : 1 ≤ P := one_le_pow₀ (by decide)
  have hrZ : 2 ≤ (r : ℤ) := by omega
  have h1 : 0 ≤ P * (2 * (m : ℤ) - (r : ℤ) - (S : ℤ)) := mul_nonneg (by linarith) (by omega)
  have h2 : 2 ≤ P * (r : ℤ) := by
    calc (2 : ℤ) = 1 * 2 := by ring
    _ ≤ P * (r : ℤ) := mul_le_mul hP hrZ (by linarith) (by linarith)
  have h3 : 0 ≤ ((k : ℤ) - 1) * (P * (r : ℤ) - 1) := mul_nonneg (by omega) (by linarith)
  linarith
