import AFTD.Prelude

/-!
# isotropic_chain_cubic_ineq

Topic: combinatorics   Node: 8926346fea1f

Provenance: helper lemma. arXiv:2611.04644, Lemma A.4 proof step 3

For every natural number m, m - 1 ≤ (1/6) m (m^2 - 1).
-/

/-- Elementary inequality (1/6) m (m^2 - 1) >= m - 1 for all natural numbers m. -/
theorem isotropic_chain_cubic_ineq (m : ℕ) :
    (m : ℝ) - 1 ≤ (1 / 6 : ℝ) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  push_cast
  have hpoly : (1 / 6 : ℝ) * ((m : ℝ) + 1 + 1) * (((m : ℝ) + 1 + 1) ^ 2 - 1) - (((m : ℝ) + 1 + 1) - 1) =
      (1 / 6 : ℝ) * (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 5) := by ring
  have hpos : 0 ≤ (1 / 6 : ℝ) * (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 5) := by positivity
  linarith
