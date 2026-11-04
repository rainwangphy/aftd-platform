import AFTD.Prelude
import AFTD.Kb.Tcs.IsNormalizedRecurrence
import AFTD.Kb.Tcs.RecurrenceProfile
import AFTD.Kb.Tcs.RecurrenceRatio
import AFTD.Kb.Tcs.HasPropertyP
import AFTD.Kb.Tcs.LinearizationCoeff
import AFTD.Kb.Tcs.RecurrenceMatrix
import AFTD.Kb.Tcs.RecurrencePoly

/-!
# op_940_dim2_property_p_of_ratio_condition

Topic: combinatorics   Node: bd1d25f51bc4

Provenance: original. Related work: arXiv:2611.01561 Sec. 6

For N = 2 and any normalized recurrence coefficients a, b, c : Fin 3 → ℝ, property (P) holds whenever the profile at 1 multiplied by (1 + r_1 * r_2) plus r_2 * (1 - r_2) is at most 1, where r_1 and r_2 are the ratio values at indices 1 and 2.
-/

lemma op_940_dim2_num_eq_one_sub (a b c : Fin 3 → ℝ) (hrec : is_normalized_recurrence 2 a b c) :
    a 1 * c 2 + b 2 * b 2 - b 1 * b 2 - c 1 =
    1 - (recurrence_profile 2 b c ⟨1, by decide⟩ *
      (1 + recurrence_ratio 2 b c ⟨1, by decide⟩ * recurrence_ratio 2 b c ⟨2, by decide⟩) +
      recurrence_ratio 2 b c ⟨2, by decide⟩ * (1 - recurrence_ratio 2 b c ⟨2, by decide⟩)) := by
  rcases hrec with ⟨ha0, hb0, hc0, ha2, hsum, ha_pos, hc_pos, hb_nonneg⟩
  have h2 : (2 : Fin 3) = ⟨2, by decide⟩ := rfl
  have ha2' : a 2 = 0 := by rw [h2]; exact ha2
  have hsum1 : a 1 + b 1 + c 1 = 1 := hsum 1
  have hsum2 : a 2 + b 2 + c 2 = 1 := hsum 2
  have hb2c2 : b 2 + c 2 = 1 := by linarith [ha2', hsum2]
  have hc1_pos : 0 < c 1 := hc_pos 1 (by decide)
  have hb1_nonneg : 0 ≤ b 1 := hb_nonneg 1
  have hbc1_pos : 0 < b 1 + c 1 := by linarith
  have hbc1_ne : b 1 + c 1 ≠ 0 := ne_of_gt hbc1_pos
  dsimp [recurrence_profile, recurrence_ratio]
  have hr2 : c 2 / (b 2 + c 2) = c 2 := by rw [hb2c2, div_one]
  rw [hr2]
  have hr1 : (b 1 + c 1) * (1 + c 1 / (b 1 + c 1) * c 2) = b 1 + c 1 + c 1 * c 2 := by
    calc (b 1 + c 1) * (1 + c 1 / (b 1 + c 1) * c 2)
      _ = (b 1 + c 1) * 1 + (b 1 + c 1) * (c 1 / (b 1 + c 1) * c 2) := mul_add _ _ _
      _ = (b 1 + c 1) + ((b 1 + c 1) * (c 1 / (b 1 + c 1))) * c 2 := by ring
      _ = (b 1 + c 1) + c 1 * c 2 := by rw [mul_div_cancel₀ _ hbc1_ne]
  rw [hr1]
  linear_combination c 2 * hsum1 + (-b 1 + b 2 - c 2 + 1) * hb2c2

lemma op_940_dim2_coeff_2_2_0 (a b c : Fin 3 → ℝ) :
    linearization_coeff 2 a b c 2 2 0 = (1 / a 1) * (c 1 * c 2) := by
  dsimp [linearization_coeff, recurrence_poly]
  simp only [map_smul, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_one]
  dsimp [recurrence_matrix]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
  simp only [Fin.ext_iff]
  norm_num
  left
  ring

lemma op_940_dim2_coeff_2_2_1 (a b c : Fin 3 → ℝ) :
    linearization_coeff 2 a b c 2 2 1 = (1 / a 1) * (b 2 * c 2) := by
  dsimp [linearization_coeff, recurrence_poly]
  simp only [map_smul, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_one]
  dsimp [recurrence_matrix]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
  simp only [Fin.ext_iff]
  norm_num
  left
  ring

lemma op_940_dim2_coeff_2_2_2 (a b c : Fin 3 → ℝ) :
    linearization_coeff 2 a b c 2 2 2 =
    (1 / a 1) * (a 1 * c 2 + b 2 * b 2 - b 1 * b 2 - c 1) := by
  dsimp [linearization_coeff, recurrence_poly]
  simp only [map_smul, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_one]
  dsimp [recurrence_matrix]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
  simp only [Fin.ext_iff]
  norm_num
  left
  ring

lemma op_940_dim2_coeff_2_others (a b c : Fin 3 → ℝ) (hrec : is_normalized_recurrence 2 a b c) :
    linearization_coeff 2 a b c 2 0 0 = 0 ∧
    linearization_coeff 2 a b c 2 0 1 = 0 ∧
    linearization_coeff 2 a b c 2 0 2 = 1 ∧
    linearization_coeff 2 a b c 2 1 0 = 0 ∧
    linearization_coeff 2 a b c 2 1 1 = c 2 ∧
    linearization_coeff 2 a b c 2 1 2 = b 2 := by
  rcases hrec with ⟨ha0, hb0, hc0, ha2, hsum, ha_pos, hc_pos, hb_nonneg⟩
  have h0 : (0 : Fin 3) = ⟨0, by decide⟩ := rfl
  have ha0' : a 0 = 1 := by rw [h0]; exact ha0
  have hb0' : b 0 = 0 := by rw [h0]; exact hb0
  have ha1_pos : 0 < a 1 := ha_pos 1 (by decide)
  have ha1_ne : a 1 ≠ 0 := ne_of_gt ha1_pos
  dsimp [linearization_coeff, recurrence_poly]
  simp only [map_smul, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_one]
  dsimp [recurrence_matrix]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
  simp only [Fin.ext_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha0', hb0']; norm_num
  · rw [ha0', hb0']; norm_num
  · rw [ha0', hb0']; norm_num [ha1_ne]
  · rw [ha0', hb0']; norm_num
  · rw [ha0', hb0']; norm_num [ha1_ne]
  · rw [ha0', hb0']; norm_num [ha1_ne]

/-- Sufficient algebraic criterion for property (P) when N = 2. -/
theorem op_940_dim2_property_p_of_ratio_condition
    (a b c : Fin 3 → ℝ)
    (hrec : is_normalized_recurrence 2 a b c)
    (hineq : recurrence_profile 2 b c ⟨1, by decide⟩ *
      (1 + recurrence_ratio 2 b c ⟨1, by decide⟩ * recurrence_ratio 2 b c ⟨2, by decide⟩) +
      recurrence_ratio 2 b c ⟨2, by decide⟩ * (1 - recurrence_ratio 2 b c ⟨2, by decide⟩) ≤ 1) :
    has_property_p 2 a b c := by
  intro m n k
  rcases hrec with ⟨ha0, hb0, hc0, ha2, hsum, ha_pos, hc_pos, hb_nonneg⟩
  have hrec' : is_normalized_recurrence 2 a b c := ⟨ha0, hb0, hc0, ha2, hsum, ha_pos, hc_pos, hb_nonneg⟩
  have h0 : (0 : Fin 3) = ⟨0, by decide⟩ := rfl
  have ha0' : a 0 = 1 := by rw [h0]; exact ha0
  have hb0' : b 0 = 0 := by rw [h0]; exact hb0
  have ha1_pos : 0 < a 1 := ha_pos 1 (by decide)
  have ha1_inv_nonneg : 0 ≤ (1 / a 1) := by
    rw [one_div]
    exact le_of_lt (inv_pos.mpr ha1_pos)
  have hc1_nonneg : 0 ≤ c 1 := le_of_lt (hc_pos 1 (by decide))
  have hc2_nonneg : 0 ≤ c 2 := le_of_lt (hc_pos 2 (by decide))
  have hb2_nonneg : 0 ≤ b 2 := hb_nonneg 2
  fin_cases m
  · dsimp [linearization_coeff, recurrence_poly]
    simp only [Polynomial.aeval_one]
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  · dsimp [linearization_coeff, recurrence_poly]
    simp only [Polynomial.aeval_X]
    dsimp [recurrence_matrix]
    fin_cases n <;> fin_cases k <;> norm_num
    · rw [hb0']
    · rw [ha0']; norm_num
    · exact le_of_lt (hc_pos 1 (by decide))
    · exact hb_nonneg 1
    · exact le_of_lt (ha_pos 1 (by decide))
    · exact le_of_lt (hc_pos 2 (by decide))
    · exact hb_nonneg 2
  · obtain ⟨h00, h01, h02, h10, h11, h12⟩ := op_940_dim2_coeff_2_others a b c hrec'
    fin_cases n <;> fin_cases k
    · change 0 ≤ linearization_coeff 2 a b c 2 0 0
      rw [h00]
    · change 0 ≤ linearization_coeff 2 a b c 2 0 1
      rw [h01]
    · change 0 ≤ linearization_coeff 2 a b c 2 0 2
      rw [h02]; norm_num
    · change 0 ≤ linearization_coeff 2 a b c 2 1 0
      rw [h10]
    · change 0 ≤ linearization_coeff 2 a b c 2 1 1
      rw [h11]; exact hc2_nonneg
    · change 0 ≤ linearization_coeff 2 a b c 2 1 2
      rw [h12]; exact hb2_nonneg
    · change 0 ≤ linearization_coeff 2 a b c 2 2 0
      rw [op_940_dim2_coeff_2_2_0]
      exact mul_nonneg ha1_inv_nonneg (mul_nonneg hc1_nonneg hc2_nonneg)
    · change 0 ≤ linearization_coeff 2 a b c 2 2 1
      rw [op_940_dim2_coeff_2_2_1]
      exact mul_nonneg ha1_inv_nonneg (mul_nonneg hb2_nonneg hc2_nonneg)
    · change 0 ≤ linearization_coeff 2 a b c 2 2 2
      rw [op_940_dim2_coeff_2_2_2, op_940_dim2_num_eq_one_sub a b c hrec']
      have hdiff : 0 ≤ 1 - (recurrence_profile 2 b c ⟨1, by decide⟩ *
        (1 + recurrence_ratio 2 b c ⟨1, by decide⟩ * recurrence_ratio 2 b c ⟨2, by decide⟩) +
        recurrence_ratio 2 b c ⟨2, by decide⟩ * (1 - recurrence_ratio 2 b c ⟨2, by decide⟩)) := by linarith
      exact mul_nonneg ha1_inv_nonneg hdiff
