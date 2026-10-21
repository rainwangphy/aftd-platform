import AFTD.Prelude

/-!
# op_258_choose_two_mul_sq_le

Topic: combinatorics   Node: cbeb3865c585

Provenance: helper lemma. step towards op_258_forces_of_forces_smul_blowup

For any γ ≥ 1 and m : ℕ, γ² * C(m, 2) ≤ C(γ * m, 2).
-/

/-- For any γ ≥ 1 and m : ℕ, γ² * C(m, 2) ≤ C(γ * m, 2) as real numbers. -/
theorem op_258_choose_two_mul_sq_le (γ m : ℕ) (hγ : 1 ≤ γ) :
    ((γ ^ 2 * m.choose 2 : ℕ) : ℝ) ≤ ((γ * m).choose 2 : ℝ) := by
  push_cast
  rw [Nat.cast_choose_two ℝ m, Nat.cast_choose_two ℝ (γ * m)]
  push_cast
  have hγ1 : (0 : ℝ) ≤ (γ : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (γ : ℝ) := Nat.one_le_cast.mpr hγ
    linarith
  have hid : (γ : ℝ) * (m : ℝ) * ((γ : ℝ) * (m : ℝ) - 1) / 2 - (γ : ℝ) ^ 2 * ((m : ℝ) * ((m : ℝ) - 1) / 2) =
      (γ : ℝ) * (m : ℝ) * ((γ : ℝ) - 1) / 2 := by ring
  have hpos : 0 ≤ (γ : ℝ) * (m : ℝ) * ((γ : ℝ) - 1) / 2 := by positivity
  linarith
