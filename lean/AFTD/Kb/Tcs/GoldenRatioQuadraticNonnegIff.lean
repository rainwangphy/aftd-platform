import AFTD.Prelude

/-!
# golden_ratio_quadratic_nonneg_iff

Topic: information   Node: 34227be61b21

Provenance: helper lemma. step towards mutual_power_divergence_subadditivity_iff_golden_ratio_exponent

For any positive exponent beta, beta^2 + beta - 1 >= 0 if and only if (Real.sqrt 5 - 1) / 2 <= beta.
-/

/-- For any positive real number beta, beta^2 + beta - 1 >= 0 if and only if beta >= (sqrt 5 - 1) / 2. -/
theorem golden_ratio_quadratic_nonneg_iff (β : ℝ) (hβ : 0 < β) :
    0 ≤ β ^ 2 + β - 1 ↔ (Real.sqrt 5 - 1) / 2 ≤ β := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have h3 : 5 ≤ (2 * β + 1) ^ 2 := by nlinarith
    have hpos : 0 < 2 * β + 1 := by linarith
    have h4 : Real.sqrt 5 ≤ 2 * β + 1 := by
      have hh : Real.sqrt 5 ≤ Real.sqrt ((2 * β + 1) ^ 2) := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq (le_of_lt hpos)] at hh
    linarith
  · intro h
    have ha : 0 ≤ 2 * β + 1 - Real.sqrt 5 := by linarith
    have hb : 0 ≤ 2 * β + 1 + Real.sqrt 5 := by
      have h' := Real.sqrt_nonneg 5
      linarith
    have h2 : 0 ≤ (2 * β + 1 - Real.sqrt 5) * (2 * β + 1 + Real.sqrt 5) :=
      mul_nonneg ha hb
    nlinarith [h2]
