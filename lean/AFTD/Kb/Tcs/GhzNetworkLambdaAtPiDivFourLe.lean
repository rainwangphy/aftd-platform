import AFTD.Prelude
import AFTD.Kb.Tcs.BellNetworkLambda
import AFTD.Kb.Tcs.GhzCorrelationVector
import AFTD.Kb.Tcs.GhzPauliCoeff

/-!
# ghz_network_lambda_at_pi_div_four_le

Topic: quantum   Node: 7ab42c3e140a

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 14

For the maximally entangled state parameter alpha = pi/4, all orthonormal frames e, f in O(3), and all setting indices mu, nu, mu', nu' in {0, 1, 2, 3}, the two-copy closed-network quantity Lambda(tau_{mu nu}, tau_{mu' nu'}) is at most 1 + sin^2(2 * (pi / 4)).
-/

open Matrix in
/-- Each row of an orthogonal 3x3 matrix is a unit vector. -/
private lemma ghz_network_lambda_at_pi_div_four_le_row_norm (e : Matrix (Fin 3) (Fin 3) ℝ)
    (he : e ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (i : Fin 3) :
    e i 0 ^ 2 + e i 1 ^ 2 + e i 2 ^ 2 = 1 := by
  have h : e * eᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp he
  have hii := congr_fun (congr_fun h i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii
  rw [Fin.sum_univ_three] at hii
  simp only [Matrix.transpose_apply] at hii
  nlinarith [hii]

open Matrix in
/-- The Pauli coefficient vector of an orthogonal frame is a unit vector. -/
private lemma ghz_network_lambda_at_pi_div_four_le_coeff_unit (e : Matrix (Fin 3) (Fin 3) ℝ)
    (he : e ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (μ : Fin 4) :
    (ghz_pauli_coeff e μ 0) ^ 2 + (ghz_pauli_coeff e μ 1) ^ 2 + (ghz_pauli_coeff e μ 2) ^ 2
      + (ghz_pauli_coeff e μ 3) ^ 2 = 1 := by
  fin_cases μ
  · simp [ghz_pauli_coeff]
  · have h := ghz_network_lambda_at_pi_div_four_le_row_norm e he 0
    simp (config := {decide := true}) [ghz_pauli_coeff]
    linarith [h]
  · have h := ghz_network_lambda_at_pi_div_four_le_row_norm e he 1
    simp (config := {decide := true}) [ghz_pauli_coeff]
    linarith [h]
  · have h := ghz_network_lambda_at_pi_div_four_le_row_norm e he 2
    simp (config := {decide := true}) [ghz_pauli_coeff]
    linarith [h]

open Matrix in
/-- At `alpha = pi/4` every GHZ correlation vector has squared norm at most one. -/
private lemma ghz_network_lambda_at_pi_div_four_le_norm_sq (e f : Matrix (Fin 3) (Fin 3) ℝ)
    (he : e ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hf : f ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (μ ν : Fin 4) :
    ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ ν ≤ 1 := by
  have hsin : Real.sin (2 * (Real.pi / 4)) = 1 := by
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have hcos : Real.cos (2 * (Real.pi / 4)) = 0 := by
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  have ha := ghz_network_lambda_at_pi_div_four_le_coeff_unit e he μ
  have hc := ghz_network_lambda_at_pi_div_four_le_coeff_unit f hf ν
  rw [dotProduct, Fin.sum_univ_three]
  simp only [ghz_correlation_vector, hsin, hcos, one_mul, zero_mul, add_zero, zero_add]
  simp only [show ((1 : Fin 3)) ≠ 0 by decide, show ((2 : Fin 3)) ≠ 0 by decide,
    show ((2 : Fin 3)) ≠ 1 by decide, if_false, if_true]
  nlinarith [sq_nonneg (ghz_pauli_coeff e μ 0 * ghz_pauli_coeff f ν 0
      - ghz_pauli_coeff e μ 3 * ghz_pauli_coeff f ν 3),
    sq_nonneg (ghz_pauli_coeff e μ 1), sq_nonneg (ghz_pauli_coeff e μ 2),
    sq_nonneg (ghz_pauli_coeff f ν 1), sq_nonneg (ghz_pauli_coeff f ν 2)]

/-- For the maximally entangled state alpha = pi/4, Lambda is at most 1 + sin^2(2*(pi/4)) = 2 for all orthonormal frames and setting quadruples. -/
theorem ghz_network_lambda_at_pi_div_four_le (e f : Matrix (Fin 3) (Fin 3) ℝ) (he : e ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hf : f ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (μ ν μ' ν' : Fin 4) :
    bell_network_lambda (ghz_correlation_vector (Real.pi / 4) e f μ ν) (ghz_correlation_vector (Real.pi / 4) e f μ' ν') ≤ 1 + Real.sin (2 * (Real.pi / 4)) ^ 2 := by
  have hsin : Real.sin (2 * (Real.pi / 4)) = 1 := by
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have hu := ghz_network_lambda_at_pi_div_four_le_norm_sq e f he hf μ ν
  have hv := ghz_network_lambda_at_pi_div_four_le_norm_sq e f he hf μ' ν'
  have hval : 1 + Real.sin (2 * (Real.pi / 4)) ^ 2 = 2 := by rw [hsin]; norm_num
  rw [hval]
  unfold bell_network_lambda
  set s := ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ ν
    + ghz_correlation_vector (Real.pi / 4) e f μ' ν' ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ' ν' with hs
  have hunn : 0 ≤ ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ ν := by
    rw [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hvnn : 0 ≤ ghz_correlation_vector (Real.pi / 4) e f μ' ν' ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ' ν' := by
    rw [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hsnn : 0 ≤ s := by rw [hs]; linarith
  have hle : s ≤ 2 := by rw [hs]; linarith
  have hsq : Real.sqrt (s ^ 2 - 4 * (ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ' ν') ^ 2) ≤ s := by
    have h1 : s ^ 2 - 4 * (ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ' ν') ^ 2 ≤ s ^ 2 := by
      nlinarith [sq_nonneg (ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ' ν')]
    have h2 : Real.sqrt (s ^ 2 - 4 * (ghz_correlation_vector (Real.pi / 4) e f μ ν ⬝ᵥ ghz_correlation_vector (Real.pi / 4) e f μ' ν') ^ 2) ≤ Real.sqrt (s ^ 2) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hsnn] at h2
  linarith
