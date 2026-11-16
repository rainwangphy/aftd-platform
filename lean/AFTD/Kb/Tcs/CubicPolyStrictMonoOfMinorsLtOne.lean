import AFTD.Prelude

/-!
# cubic_poly_strict_mono_of_minors_lt_one

Topic: combinatorics   Node: 0169e31a5e39

Provenance: formalization of a published result. Source: arXiv:2611.14694, Proof of Proposition 5.1 -- Real positive definite counterexamples to a monotonicity conjecture for the q-permanent

For any real numbers x, y, z satisfying x^2 < 1, y^2 < 1, and (x, y, z) ≠ (0, 0, 0), the cubic polynomial function mapping q to 1 + (x^2 + y^2) * q + 2 * x * y * z * q^2 + z^2 * q^3 is strictly increasing on ℝ.
-/

/-- The cubic polynomial 1 + (x^2 + y^2)q + 2xyz q^2 + z^2 q^3 is strictly increasing on ℝ whenever x^2 < 1, y^2 < 1, and (x, y, z) ≠ (0, 0, 0). -/
theorem cubic_poly_strict_mono_of_minors_lt_one
    (x y z : ℝ) (hx : x ^ 2 < 1) (hy : y ^ 2 < 1) (hne : (x, y, z) ≠ (0, 0, 0)) :
    StrictMono (fun q : ℝ => 1 + (x ^ 2 + y ^ 2) * q + 2 * x * y * z * q ^ 2 + z ^ 2 * q ^ 3) := by
  intro q1 q2 hlt
  have hB : 0 < (x ^ 2 + y ^ 2) + 2 * x * y * z * (q1 + q2)
      + z ^ 2 * (q1 ^ 2 + q1 * q2 + q2 ^ 2) := by
    by_cases hz : z = 0
    · have hApos : 0 < x ^ 2 + y ^ 2 := by
        by_contra h
        have hsum : x ^ 2 + y ^ 2 = 0 := by
          have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
          linarith
        have hx0 : x = 0 := by nlinarith [sq_nonneg x]
        have hy0 : y = 0 := by nlinarith [sq_nonneg y]
        apply hne
        simp [hx0, hy0, hz]
      simpa [hz] using hApos
    · have hkey : 0 ≤ 3 * (x ^ 2 + y ^ 2) - 4 * x ^ 2 * y ^ 2 := by
        have h1 : 0 ≤ x ^ 2 * (1 - y ^ 2) := by
          exact mul_nonneg (sq_nonneg x) (by linarith)
        have h2 : 0 ≤ y ^ 2 * (1 - x ^ 2) := by
          exact mul_nonneg (sq_nonneg y) (by linarith)
        nlinarith
      have h12 :
          12 * ((x ^ 2 + y ^ 2) + 2 * x * y * z * (q1 + q2)
            + z ^ 2 * (q1 ^ 2 + q1 * q2 + q2 ^ 2))
            = (3 * z * (q1 + q2) + 4 * x * y) ^ 2
              + 4 * (3 * (x ^ 2 + y ^ 2) - 4 * x ^ 2 * y ^ 2)
              + 3 * z ^ 2 * (q2 - q1) ^ 2 := by
        ring
      have hz2 : 0 < z ^ 2 := sq_pos_of_ne_zero hz
      have hd2 : 0 < (q2 - q1) ^ 2 := by
        apply sq_pos_of_ne_zero
        linarith
      have hlast : 0 < 3 * z ^ 2 * (q2 - q1) ^ 2 := by positivity
      have hsq : 0 ≤ (3 * z * (q1 + q2) + 4 * x * y) ^ 2 := sq_nonneg _
      have hres : 0 ≤ 4 * (3 * (x ^ 2 + y ^ 2) - 4 * x ^ 2 * y ^ 2) := by positivity
      have hrhs : 0 < (3 * z * (q1 + q2) + 4 * x * y) ^ 2
              + 4 * (3 * (x ^ 2 + y ^ 2) - 4 * x ^ 2 * y ^ 2)
              + 3 * z ^ 2 * (q2 - q1) ^ 2 := by linarith
      nlinarith
  have hdiff :
      (1 + (x ^ 2 + y ^ 2) * q2 + 2 * x * y * z * q2 ^ 2 + z ^ 2 * q2 ^ 3)
        - (1 + (x ^ 2 + y ^ 2) * q1 + 2 * x * y * z * q1 ^ 2 + z ^ 2 * q1 ^ 3)
      = (q2 - q1) * ((x ^ 2 + y ^ 2) + 2 * x * y * z * (q1 + q2)
        + z ^ 2 * (q1 ^ 2 + q1 * q2 + q2 ^ 2)) := by
    ring
  have hpos : 0 < (1 + (x ^ 2 + y ^ 2) * q2 + 2 * x * y * z * q2 ^ 2 + z ^ 2 * q2 ^ 3)
        - (1 + (x ^ 2 + y ^ 2) * q1 + 2 * x * y * z * q1 ^ 2 + z ^ 2 * q1 ^ 3) := by
    rw [hdiff]
    exact mul_pos (by linarith) hB
  linarith
