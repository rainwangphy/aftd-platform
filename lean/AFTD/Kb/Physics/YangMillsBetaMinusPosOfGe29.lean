import AFTD.Prelude
import AFTD.Kb.Physics.YangMillsBetaMinus

/-!
# yang_mills_beta_minus_pos_of_ge_29

Topic: classical_fields   Node: 4227f1e34b7f

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:170

For every natural number d >= 29, beta_-(d) is strictly positive.
-/

/-- For all integers d >= 29, the denominator parameter beta_-(d) is strictly positive. -/
theorem yang_mills_beta_minus_pos_of_ge_29 (d : ℕ) (hd : 29 ≤ d) :
    0 < yang_mills_beta_minus (d : ℝ) := by
  unfold yang_mills_beta_minus
  have hd_real : (29 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 < 2 * ((d : ℝ) - 4) := by linarith
  apply div_pos _ (by norm_num)
  rw [sub_pos, Real.sqrt_lt' hpos]
  nlinarith
