import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.DiscreteDist

/-!
# two_box_risky_value_mean

Topic: online_algorithms   Node: 0bb7cb6805ca

Provenance: helper lemma. step towards two_box_counterexample_family

The mean of the risky distribution is 1.
-/

/-- The expected value of box 1's value distribution is exactly `1`. -/
theorem two_box_risky_value_mean (M : ℕ) (hM : 1 < M) :
    ∑ v ∈ (two_box_risky_value_dist M hM).support, (two_box_risky_value_dist M hM).prob v * v = 1 := by
  have hM0 : (0 : ℝ) ≠ (M : ℝ) := by
    have : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    linarith
  simp only [two_box_risky_value_dist]
  rw [Finset.sum_pair hM0]
  simp only [if_true, if_neg (Ne.symm hM0), mul_zero, zero_add]
  have hMpos : (M : ℝ) ≠ 0 := Ne.symm hM0
  field_simp
