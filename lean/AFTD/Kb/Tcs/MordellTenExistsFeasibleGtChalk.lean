import AFTD.Prelude
import AFTD.Kb.Tcs.MordellTenIntegerNormSum
import AFTD.Kb.Tcs.MordellTenIntegerWitnessIneq

/-!
# mordell_ten_exists_feasible_gt_chalk

Topic: combinatorics   Node: 6a12871ea3a6

Provenance: helper lemma. arXiv:2611.03088 Section 5.1

There exists a configuration of ten points z : Fin 10 → ℂ in the complex plane satisfying ∑ i : Fin 10, ‖z i‖^2 = 10 such that ∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖^2 > (10 : ℝ)^45 / (9 : ℝ)^36.
-/

open Finset

def mordell_ten_exists_feasible_gt_chalk_W : Fin 10 → ℤ × ℤ := ![(11183, 0), (-11183, 0),
  (32765, 14669), (32765, -14669), (-32765, 14669), (-32765, -14669),
  (12323, 31572), (12323, -31572), (-12323, 31572), (-12323, -31572)]

lemma mordell_ten_exists_feasible_gt_chalk_prod_pair_scale (c : ℝ) (d : Fin 10 → Fin 10 → ℝ) :
    (∏ i : Fin 10, ∏ j : Fin 10 with i < j, (c * d i j)) =
      c ^ 45 * ∏ i : Fin 10, ∏ j : Fin 10 with i < j, d i j := by
  have h1 : ∀ i : Fin 10, (∏ j : Fin 10 with i < j, (c * d i j)) =
      c ^ #(filter (fun j : Fin 10 => i < j) univ) * ∏ j : Fin 10 with i < j, d i j := by
    intro i
    rw [prod_mul_distrib, prod_const]
  simp_rw [h1]
  rw [prod_mul_distrib]
  rw [prod_pow_eq_pow_sum]
  have h2 : (∑ i : Fin 10, #(filter (fun j : Fin 10 => i < j) univ)) = 45 := by decide
  rw [h2]

lemma mordell_ten_exists_feasible_gt_chalk_ineq_step (q P : ℝ) (hq : 0 < q)
    (hP : (9 : ℝ) ^ 36 * P > q ^ 45) :
    (10 / q) ^ 45 * P > (10 : ℝ) ^ 45 / (9 : ℝ) ^ 36 := by
  have h9 : (0 : ℝ) < (9 : ℝ) ^ 36 := by positivity
  have hq45 : (0 : ℝ) < q ^ 45 := by positivity
  rw [div_pow]
  rw [gt_iff_lt] at *
  rw [div_lt_iff₀ h9]
  rw [mul_assoc]
  rw [mul_comm P (9 ^ 36)]
  rw [div_mul_eq_mul_div]
  rw [lt_div_iff₀ hq45]
  nlinarith

/-- Existence of a feasible 10-point configuration beating the centered regular polygon value. -/
lemma mordell_ten_exists_feasible_gt_chalk :
    ∃ z : Fin 10 → ℂ, (∑ i : Fin 10, ‖z i‖ ^ 2 = 10) ∧
      (∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖ ^ 2) > (10 : ℝ) ^ 45 / (9 : ℝ) ^ 36 := by
  let W := mordell_ten_exists_feasible_gt_chalk_W
  let c : ℝ := Real.sqrt (10 / 9999608174)
  let z : Fin 10 → ℂ := fun i => (c : ℂ) * Complex.mk ((W i).1 : ℝ) ((W i).2 : ℝ)
  use z
  have hc2 : c ^ 2 = 10 / 9999608174 := by
    apply Real.sq_sqrt
    positivity
  have hnorm : ∀ i : Fin 10, ‖z i‖ ^ 2 = c ^ 2 * (((W i).1 : ℝ) ^ 2 + ((W i).2 : ℝ) ^ 2) := by
    intro i
    rw [← Complex.normSq_eq_norm_sq]
    dsimp [z]
    rw [Complex.normSq.map_mul, Complex.normSq_ofReal, Complex.normSq_mk, sq, sq, sq]
  have hsum : ∑ i : Fin 10, ‖z i‖ ^ 2 = 10 := by
    simp_rw [hnorm, hc2]
    rw [← Finset.mul_sum]
    have h : (∑ i : Fin 10, (((W i).1 : ℝ) ^ 2 + ((W i).2 : ℝ) ^ 2)) = (9999608174 : ℝ) := by
      have h0 := mordell_ten_integer_norm_sum
      have h_cast := congr_arg (fun (x : ℤ) => (x : ℝ)) h0
      push_cast at h_cast
      exact h_cast
    rw [h]
    exact div_mul_cancel₀ 10 (by norm_num)
  refine ⟨hsum, ?_⟩
  have hdiff : ∀ i j : Fin 10,
      ‖z i - z j‖ ^ 2 = c ^ 2 * (((W i).1 - (W j).1 : ℝ) ^ 2 + ((W i).2 - (W j).2 : ℝ) ^ 2) := by
    intro i j
    rw [← Complex.normSq_eq_norm_sq]
    dsimp [z]
    rw [← mul_sub]
    rw [Complex.normSq.map_mul, Complex.normSq_ofReal, sq]
    congr 1
    rw [Complex.normSq_apply]
    simp [sq]
  simp_rw [hdiff, hc2]
  rw [mordell_ten_exists_feasible_gt_chalk_prod_pair_scale]
  have hP : (9 : ℝ) ^ 36 * ∏ i : Fin 10, ∏ j : Fin 10 with i < j,
      (((W i).1 - (W j).1 : ℝ) ^ 2 + ((W i).2 - (W j).2 : ℝ) ^ 2) > (9999608174 : ℝ) ^ 45 := by
    have h0 := mordell_ten_integer_witness_ineq
    have h_cast : ((9 : ℤ) ^ 36 * ∏ i : Fin 10, ∏ j : Fin 10 with i < j,
        (((W i).1 - (W j).1) ^ 2 + ((W i).2 - (W j).2) ^ 2) : ℝ) > (((9999608174 : ℤ) : ℝ) ^ 45) := by
      exact_mod_cast h0
    push_cast at h_cast
    exact h_cast
  exact mordell_ten_exists_feasible_gt_chalk_ineq_step 9999608174 _ (by norm_num) hP
