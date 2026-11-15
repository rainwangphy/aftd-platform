import AFTD.Prelude

/-!
# op_1721_eventual_log_concavity_failure

Topic: combinatorics   Node: 8f49239e11e9

Provenance: helper lemma. arXiv:2106.02330, OP-1721

For every real p strictly between 0 and 1, let q = 1 - p, r(d) = Nat.ceil (d / q^d), u(d) = q^(2d), b(d, j) = (r(d).choose j : ℝ) * u(d)^j * (1 - u(d))^(r(d) - j) * q^j + (r(d).choose (j + 1) : ℝ) * u(d)^(j + 1) * (1 - u(d))^(r(d) - (j + 1)) * (1 - q^(j + 1)), and ratio(d) = (b(d, d))^2 / (b(d, d - 1) * b(d, d + 1)). If ratio(d) tends to 4 * q / (1 + q)^2 as d tends to infinity, then there exists d0 such that for all d >= d0, ratio(d) < 1, failing log-concavity.
-/

/-- Convergence to 4q/(1+q)^2 implies eventual failure of matching-number log-concavity -/
theorem op_1721_eventual_log_concavity_failure (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let q := 1 - p
    let r (d : ℕ) := Nat.ceil ((d : ℝ) / q ^ d)
    let u (d : ℕ) := q ^ (2 * d)
    let b (d : ℕ) (j : ℕ) :=
      (r d).choose j * u d ^ j * (1 - u d) ^ (r d - j) * q ^ j +
        (r d).choose (j + 1) * u d ^ (j + 1) * (1 - u d) ^ (r d - (j + 1)) * (1 - q ^ (j + 1))
    let ratio (d : ℕ) := (b d d) ^ 2 / (b d (d - 1) * b d (d + 1))
    Filter.Tendsto ratio Filter.atTop (nhds (4 * q / (1 + q) ^ 2)) →
      ∃ d₀ : ℕ, ∀ d ≥ d₀, ratio d < 1 := by
  intro q r u b ratio h
  have hq0 : 0 < q := by
    show 0 < 1 - p
    linarith
  have hq1 : q < 1 := by
    show 1 - p < 1
    linarith
  have hlt : 4 * q / (1 + q) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hq0), hq1]
  have hev := (tendsto_order.1 h).2 1 hlt
  rwa [Filter.eventually_atTop] at hev
