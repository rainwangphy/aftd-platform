import AFTD.Prelude
import AFTD.Kb.Tcs.PellNumber

/-!
# pell_number_closed_form

Topic: automata   Node: 5689178beb2e

Provenance: formalization of a published result. Source: arXiv:2610.08525 Appendix A

For every natural number m, twice the m-th Pell number equals ((1 + Real.sqrt 2) ^ m - (1 - Real.sqrt 2) ^ m) / Real.sqrt 2.
-/

/-- Closed-form Binet-type expression for the Pell numbers in terms of 1 ± √2. -/
theorem pell_number_closed_form (m : ℕ) :
    (2 * (pell_number m : ℝ)) =
      ((1 + Real.sqrt 2) ^ m - (1 - Real.sqrt 2) ^ m) / Real.sqrt 2 := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set a : ℝ := 1 + Real.sqrt 2 with ha_def
  set b : ℝ := 1 - Real.sqrt 2 with hb_def
  have hsqrt2_ne : (2 * Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have a_sq : a ^ 2 = 2 * a + 1 := by rw [ha_def]; nlinarith
  have b_sq : b ^ 2 = 2 * b + 1 := by rw [hb_def]; nlinarith
  have closed_form : ∀ m : ℕ, (pell_number m : ℝ) = (a ^ m - b ^ m) / (2 * Real.sqrt 2) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [pell_number.eq_1]
    | one =>
      have h1 : a ^ 1 - b ^ 1 = 2 * Real.sqrt 2 := by
        rw [pow_one, pow_one, ha_def, hb_def]; ring
      rw [pell_number.eq_2, h1, div_self hsqrt2_ne]
      norm_num
    | more k ih1 ih2 =>
      have hstep : a ^ (k + 2) - b ^ (k + 2) = 2 * (a ^ (k + 1) - b ^ (k + 1)) + (a ^ k - b ^ k) := by
        rw [pow_add, pow_add, pow_add, pow_add, a_sq, b_sq]
        ring
      change ((pell_number (k + 2) : ℕ) : ℝ) = (a ^ (k + 2) - b ^ (k + 2)) / (2 * Real.sqrt 2)
      rw [show k + 2 = k.succ.succ from rfl, pell_number.eq_3, hstep]
      push_cast
      rw [ih1, ih2]
      ring
  rw [closed_form m]
  calc 2 * ((a ^ m - b ^ m) / (2 * Real.sqrt 2))
    _ = (2 * (a ^ m - b ^ m)) / (2 * Real.sqrt 2) := mul_div_assoc' 2 (a ^ m - b ^ m) (2 * Real.sqrt 2)
    _ = (a ^ m - b ^ m) / Real.sqrt 2 := mul_div_mul_left (a ^ m - b ^ m) (Real.sqrt 2) (by norm_num)
