import AFTD.Prelude

/-!
# bivalued_rounding_odd_mms_arithmetic

Topic: fair_division   Node: 190eb570b678

Provenance: helper lemma. Elementary arithmetic for the bivalued two-agent rounding route in IN-570.

The odd-count MMS lower bound dominates the cost bound for a balanced bundle.
-/

theorem bivalued_rounding_odd_mms_arithmetic(k h : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    (k + 1 : ℝ) + d * (((h + 1) / 2 : ℕ) : ℝ) ≤
      (1 + d / 2) * ((k + 1 : ℝ) + d * ((h - k : ℕ) : ℝ)) := by
  have hc : 2 * ((h + 1) / 2) ≤ k + 1 + 2 * (h - k) := by omega
  have hcr : (2 : ℝ) * (((h + 1) / 2 : ℕ) : ℝ) ≤
      (k : ℝ) + 1 + 2 * ((h - k : ℕ) : ℝ) := by
    exact_mod_cast hc
  have harr : 0 ≤ (k : ℝ) + 1 + 2 * ((h - k : ℕ) : ℝ) -
      2 * (((h + 1) / 2 : ℕ) : ℝ) := by linarith
  have hmul := mul_nonneg hd harr
  have hsq : 0 ≤ d * d * ((h - k : ℕ) : ℝ) := by positivity
  nlinarith
