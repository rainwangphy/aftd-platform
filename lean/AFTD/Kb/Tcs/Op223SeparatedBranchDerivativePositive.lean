import AFTD.Prelude

/-!
# op223_separated_branch_derivative_positive

Topic: graphs   Node: 074579e73e12

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; scalar inequality for a separated-branch derivative argument

For finite nonnegative vectors p and q, suppose 0 ≤ r < 1, q is pointwise at least r times p, and equality holds at u, v, and j. If p at u exceeds p at v and p at j is positive, then the product of q's u-v difference and its j entry, divided by one plus its squared norm, is strictly smaller than the analogous quantity for p.
-/

open scoped Classical

theorem op223_separated_branch_derivative_positive {ι : Type*} [Fintype ι] (p q : ι → ℝ) (u v j : ι) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpj : 0 < p j) (huv : p v < p u) (hbound : ∀ i, r * p i ≤ q i) (hqu : q u = r * p u) (hqv : q v = r * p v) (hqj : q j = r * p j) : (q u - q v) * q j / (1 + ∑ i, q i ^ 2) < (p u - p v) * p j / (1 + ∑ i, p i ^ 2) := by
  have _ := hq
  have hDp : 0 < 1 + ∑ i, p i ^ 2 := by positivity
  have hDq : 0 < 1 + ∑ i, q i ^ 2 := by positivity
  rw [div_lt_div_iff₀ hDq hDp]
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hsum : r ^ 2 * ∑ i, p i ^ 2 ≤ ∑ i, q i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h1 : 0 ≤ r * p i := mul_nonneg hr0 (hp i)
    have h2 : (r * p i) ^ 2 ≤ q i ^ 2 := by nlinarith [hbound i]
    have h3 : (r * p i) ^ 2 = r ^ 2 * p i ^ 2 := mul_pow r (p i) 2
    linarith
  have hD : r ^ 2 * (1 + ∑ i, p i ^ 2) < 1 + ∑ i, q i ^ 2 := by linarith
  have hN : 0 < (p u - p v) * p j := by
    have : 0 < p u - p v := sub_pos.mpr huv
    positivity
  have hnum : (q u - q v) * q j = r ^ 2 * ((p u - p v) * p j) := by
    rw [hqu, hqv, hqj]
    ring
  rw [hnum]
  nlinarith
