import AFTD.Prelude

/-!
# bivalued_rounding_even_mms_arithmetic

Topic: fair_division   Node: b0d616b4f560

Provenance: helper lemma. Elementary arithmetic for the bivalued two-agent rounding route in IN-570.

The even-count MMS lower bound dominates the cost bound for a balanced bundle.
-/

theorem bivalued_rounding_even_mms_arithmetic(k h : ℕ) (d : ℝ) (hk : 1 ≤ k) (hd : 0 ≤ d) :
    (k : ℝ) + d * (((h + 1) / 2 : ℕ) : ℝ) ≤
      (1 + d / 2) * ((k : ℝ) + d * (h : ℝ) / 2) := by
  have hc : 2 * ((h + 1) / 2) ≤ h + 1 := by omega
  have hcr : (2 : ℝ) * (((h + 1) / 2 : ℕ) : ℝ) ≤ (h : ℝ) + 1 := by
    exact_mod_cast hc
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have harr : 0 ≤ (k : ℝ) + (h : ℝ) - 2 * (((h + 1) / 2 : ℕ) : ℝ) := by linarith
  have hmul := mul_nonneg hd harr
  have hsq : 0 ≤ d * d * (h : ℝ) := by positivity
  nlinarith
