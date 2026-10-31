import AFTD.Prelude

/-!
# golden_ratio_exponent_pos_and_lt_one

Topic: information   Node: 9e11cb9d7cb6

Provenance: helper lemma. step towards mutual_power_divergence_subadditivity_iff_golden_ratio_exponent

The golden-ratio exponent (Real.sqrt 5 - 1) / 2 satisfies 0 < (Real.sqrt 5 - 1) / 2 < 1.
-/

/-- The golden-ratio conjugate exponent (sqrt 5 - 1) / 2 belongs to the open unit interval (0, 1). -/
theorem golden_ratio_exponent_pos_and_lt_one :
    0 < (Real.sqrt 5 - 1) / 2 ∧ (Real.sqrt 5 - 1) / 2 < 1 := by
  have h1 : (1 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor <;> linarith
