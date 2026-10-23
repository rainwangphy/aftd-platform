import AFTD.Prelude

/-!
# op_258_choose_two_sub_pow

Topic: combinatorics   Node: 2ed2063f706e

Provenance: helper lemma. step towards op_258_exists_divergent_capacity_covering

For any natural l ≥ 3, 2^{l-1} ≤ C(2^l, 2) - 2^{2l - 2}.
-/

/-- For l ≥ 3, the binomial coefficient C(2^l, 2) exceeds 2^{2l - 2} by at least 2^{l - 1}. -/
theorem op_258_choose_two_sub_pow (l : ℕ) (hl : 3 ≤ l) :
    (2 : ℝ)^(l - 1) ≤ ((2^l).choose 2 : ℝ) - (2 : ℝ)^(2 * l - 2) := by
  have hchoose : ((2^l).choose 2 : ℝ) = (2 : ℝ)^l * ((2 : ℝ)^l - 1) / 2 := by
    have := Nat.cast_choose_two ℝ (2^l)
    push_cast at this
    exact this
  set y : ℝ := (2 : ℝ)^(l - 1)
  have hl1 : l = (l - 1) + 1 := by omega
  have hl2 : 2 * l - 2 = (l - 1) * 2 := by omega
  have hyl : (2 : ℝ)^l = 2 * y := by
    rw [hl1, pow_succ]
    ring
  have hy2l : (2 : ℝ)^(2 * l - 2) = y^2 := by
    rw [hl2, pow_mul]
  have hy_ge_4 : 4 ≤ y := by
    have : 2 ≤ l - 1 := by omega
    have h2 : (2 : ℝ)^2 ≤ (2 : ℝ)^(l - 1) := by
      gcongr
      norm_num
    norm_num at h2
    exact h2
  rw [hchoose, hyl, hy2l]
  nlinarith
