import AFTD.Prelude
import AFTD.Kb.Tcs.GaleSigmaThree

/-!
# sphere_three_partition_ratio_lt_threshold

Topic: combinatorics   Node: f7566bfbb965

Provenance: helper lemma. arXiv:2610.28828 -- A counterexample to Gale's conjecture in $\mathbb{R}^3$, Theorem 2

The four-partition diameter ratio constant of the unit 2-sphere, namely sqrt((3 + sqrt(3)) / 6), is strictly less than 0.88928.
-/

/-- The four-partition diameter ratio constant of the unit sphere sqrt((3 + sqrt 3) / 6) is strictly less than 0.88928. -/
theorem sphere_three_partition_ratio_lt_threshold :
    gale_sigma_three < (88928 / 100000 : ℝ) := by
  have h3 : Real.sqrt 3 < (26 / 15 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 26 / 15)]
    norm_num
  have h0 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [gale_sigma_three, Real.sqrt_lt' (by norm_num : (0:ℝ) < 88928 / 100000)]
  nlinarith
