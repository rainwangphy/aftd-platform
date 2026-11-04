import AFTD.Prelude
import AFTD.Kb.Tcs.IsNormalizedRecurrence
import AFTD.Kb.Tcs.IsLogConcaveNewton
import AFTD.Kb.Tcs.RecurrenceProfile
import AFTD.Kb.Tcs.RecurrenceRatio
import AFTD.Kb.Tcs.HasPropertyP
import AFTD.Kb.Tcs.NewtonCoeff
import AFTD.Kb.Tcs.LinearizationCoeff
import AFTD.Kb.Tcs.RecurrenceMatrix
import AFTD.Kb.Tcs.RecurrencePoly

/-!
# op_940_decreasing_ratios_not_all_property_p

Topic: combinatorics   Node: 450b34892187

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 6, Other ratios

It is not the case that for every N ≥ 2 and all normalized recurrence coefficients a, b, c : Fin (N + 1) → ℝ with log-concave Newton profile and ratio sequence recurrence_ratio N b c non-increasing on positive indices (meaning that for all i j : Fin (N + 1) with 0 < i.val and i.val ≤ j.val, recurrence_ratio N b c j ≤ recurrence_ratio N b c i), property (P) holds.
-/

noncomputable def op_940_decreasing_ratios_not_all_property_p_a (i : Fin 3) : ℝ :=
  if i.val = 0 then 1
  else if i.val = 1 then 1/2
  else 0

noncomputable def op_940_decreasing_ratios_not_all_property_p_b (i : Fin 3) : ℝ :=
  if i.val = 2 then 1/4
  else 0

noncomputable def op_940_decreasing_ratios_not_all_property_p_c (i : Fin 3) : ℝ :=
  if i.val = 1 then 1/2
  else if i.val = 2 then 3/4
  else 0

/-- Refutation of the decreasing-ratio property (P) conjecture for OP-940. -/
theorem op_940_decreasing_ratios_not_all_property_p :
  ¬ (∀ (N : ℕ) (hN : 2 ≤ N) (a b c : Fin (N + 1) → ℝ),
    is_normalized_recurrence N a b c →
    is_log_concave_newton N (recurrence_profile N b c) →
    (∀ (i j : Fin (N + 1)), 0 < i.val → i.val ≤ j.val →
      recurrence_ratio N b c j ≤ recurrence_ratio N b c i) →
    has_property_p N a b c) := by
  intro H
  have h_norm : is_normalized_recurrence 2 op_940_decreasing_ratios_not_all_property_p_a
      op_940_decreasing_ratios_not_all_property_p_b
      op_940_decreasing_ratios_not_all_property_p_c := by
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [op_940_decreasing_ratios_not_all_property_p_a,
        op_940_decreasing_ratios_not_all_property_p_b, op_940_decreasing_ratios_not_all_property_p_c]
    · intro i hi; fin_cases i
      · norm_num [op_940_decreasing_ratios_not_all_property_p_a]
      · norm_num [op_940_decreasing_ratios_not_all_property_p_a]
      · revert hi; norm_num
    · intro i hi; fin_cases i
      · revert hi; norm_num
      · norm_num [op_940_decreasing_ratios_not_all_property_p_c]
      · norm_num [op_940_decreasing_ratios_not_all_property_p_c]
    · intro i; fin_cases i <;> norm_num [op_940_decreasing_ratios_not_all_property_p_b]
  have h_log : is_log_concave_newton 2 (recurrence_profile 2 op_940_decreasing_ratios_not_all_property_p_b
      op_940_decreasing_ratios_not_all_property_p_c) := by
    dsimp [is_log_concave_newton]
    constructor
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rcases hk with ⟨h1, h2⟩
      interval_cases k
      · dsimp [newton_coeff]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        dsimp [recurrence_profile, op_940_decreasing_ratios_not_all_property_p_b,
          op_940_decreasing_ratios_not_all_property_p_c]
        norm_num
      · dsimp [newton_coeff]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        dsimp [recurrence_profile, op_940_decreasing_ratios_not_all_property_p_b,
          op_940_decreasing_ratios_not_all_property_p_c]
        norm_num
    · intro k hk
      rw [Finset.mem_Ico] at hk
      omega
  have h_ratio : ∀ (i j : Fin 3), 0 < i.val → i.val ≤ j.val →
      recurrence_ratio 2 op_940_decreasing_ratios_not_all_property_p_b
        op_940_decreasing_ratios_not_all_property_p_c j ≤
      recurrence_ratio 2 op_940_decreasing_ratios_not_all_property_p_b
        op_940_decreasing_ratios_not_all_property_p_c i := by
    intro i j hi hij
    fin_cases i
    · revert hi; norm_num
    · fin_cases j
      · revert hij; norm_num
      · norm_num
      · dsimp [recurrence_ratio, op_940_decreasing_ratios_not_all_property_p_b,
          op_940_decreasing_ratios_not_all_property_p_c]; norm_num
    · fin_cases j
      · revert hij; norm_num
      · revert hij; norm_num
      · norm_num
  have hP := H 2 (by norm_num) op_940_decreasing_ratios_not_all_property_p_a
    op_940_decreasing_ratios_not_all_property_p_b
    op_940_decreasing_ratios_not_all_property_p_c h_norm h_log h_ratio
  have h_nonneg : 0 ≤ linearization_coeff 2 op_940_decreasing_ratios_not_all_property_p_a
    op_940_decreasing_ratios_not_all_property_p_b
    op_940_decreasing_ratios_not_all_property_p_c 2 2 2 := hP 2 2 2
  have h_val : linearization_coeff 2 op_940_decreasing_ratios_not_all_property_p_a
      op_940_decreasing_ratios_not_all_property_p_b
      op_940_decreasing_ratios_not_all_property_p_c 2 2 2 = -1/8 := by
    dsimp [linearization_coeff, recurrence_poly]
    simp only [map_smul, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_one]
    dsimp [recurrence_matrix, op_940_decreasing_ratios_not_all_property_p_a,
      op_940_decreasing_ratios_not_all_property_p_b, op_940_decreasing_ratios_not_all_property_p_c]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
    simp only [Fin.ext_iff]
    norm_num
  rw [h_val] at h_nonneg
  norm_num at h_nonneg
