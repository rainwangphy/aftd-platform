import AFTD.Prelude
import AFTD.Kb.Tcs.DivideAndConquerUnequalRootsRecurrence
import AFTD.Kb.Tcs.DivideAndConquerRecursionTree

/-!
# master_theorem_polynomial_case_three

Topic: algorithms   Node: 99361feecc4f

Let a ≥ 0, b > 1 and c ≥ 0 be real numbers, d a natural number, and T : ℕ → ℝ a sequence with T(0) ≥ 0 satisfying the master recurrence at problem size n = b^k, namely T(k+1) = a·T(k) + c·b^{d(k+1)}. If b^d < a (the branching term dominates), then for every k ≥ 1 the value T(k) is Θ(n^{log_b a}) with n = b^k, in the explicit two-sided form (c·b^d/a)·a^k ≤ T(k) ≤ (T(0) + c·b^d/(a − b^d))·a^k.
-/

theorem master_theorem_polynomial_case_three (T : ℕ → ℝ) (a b c : ℝ) (d : ℕ)
    (hrec : ∀ k : ℕ, T (k + 1) = a * T k + c * b ^ (d * (k + 1)))
    (hT0 : 0 ≤ T 0) (ha : 0 ≤ a) (hb : 1 < b) (hc : 0 ≤ c) (hgt : b ^ d < a) :
    ∀ k : ℕ, 1 ≤ k →
      c * b ^ d / a * a ^ k ≤ T k ∧ T k ≤ (T 0 + c * b ^ d / (a - b ^ d)) * a ^ k := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hrpos : 0 < b ^ d := pow_pos hb0 d
  have hrnonneg : 0 ≤ b ^ d := le_of_lt hrpos
  have hapos : 0 < a := lt_trans hrpos hgt
  have hden : 0 < a - b ^ d := sub_pos.mpr hgt
  have hane : a ≠ b ^ d := ne_of_gt hgt
  have hsol : ∀ k : ℕ, T k = T 0 * a ^ k + c * b ^ d * ((a ^ k - (b ^ d) ^ k) / (a - b ^ d)) := by
    apply divide_and_conquer_unequal_roots_recurrence T a (b ^ d) c (T 0) hane rfl
    intro k
    rw [hrec k, pow_mul]
  intro k hk
  constructor
  · rw [hsol k]
    have hT0term : 0 ≤ T 0 * a ^ k := mul_nonneg hT0 (pow_nonneg ha k)
    have hpow : (b ^ d) ^ (k - 1) ≤ a ^ (k - 1) := pow_le_pow_left₀ hrnonneg (le_of_lt hgt) (k - 1)
    have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hak : a ^ k = a ^ (k - 1) * a := by
      conv_lhs => rw [← hk_eq]
      rw [pow_succ]
    have hrk : (b ^ d) ^ k = (b ^ d) ^ (k - 1) * (b ^ d) := by
      conv_lhs => rw [← hk_eq]
      rw [pow_succ]
    have hkey : (b ^ d) ^ k * a ≤ a ^ k * (b ^ d) := by
      rw [hak, hrk]
      nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hrnonneg (le_of_lt hapos))]
    have hterm' : a ^ k / a ≤ (a ^ k - (b ^ d) ^ k) / (a - b ^ d) := by
      rw [div_le_div_iff₀ hapos hden]
      nlinarith [hkey]
    have hterm : c * b ^ d / a * a ^ k ≤ c * b ^ d * ((a ^ k - (b ^ d) ^ k) / (a - b ^ d)) := by
      have heq : c * b ^ d / a * a ^ k = c * b ^ d * (a ^ k / a) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hterm' (mul_nonneg hc hrnonneg)
    exact le_trans hterm (le_add_of_nonneg_left hT0term)
  · have hU : (T 0 + c * b ^ d / (a - b ^ d)) * a ^ k - T k = c * b ^ d * (b ^ d) ^ k / (a - b ^ d) := by
      rw [hsol k]
      field_simp
      ring
    have hUnn : 0 ≤ c * b ^ d * (b ^ d) ^ k / (a - b ^ d) :=
      div_nonneg (mul_nonneg (mul_nonneg hc hrnonneg) (pow_nonneg hrnonneg k)) (le_of_lt hden)
    linarith [hU, hUnn]
