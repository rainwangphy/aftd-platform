import AFTD.Prelude
import AFTD.Kb.Tcs.BellNetworkLambda
import AFTD.Kb.Tcs.GhzCorrelationVector
import AFTD.Kb.Tcs.GhzPauliCoeff
import AFTD.Kb.Tcs.GhzStandardFrameLambdaLe

/-!
# ghz_closed_network_lambda_le_two

Topic: quantum   Node: 2e89658b5707

Provenance: formalization of a published result. Source: arXiv:2610.35838 Appendix B

For every parameter alpha in R, all orthonormal frames e, f in O(3), and all setting indices mu, nu, mu', nu' in {0, 1, 2, 3}, the two-copy closed-network Bell measurement quantity Lambda(tau_{mu nu}, tau_{mu' nu'}) for the generalized GHZ state is at most 2.
-/

lemma ghz_closed_network_lambda_le_two_norm_sq_bound (s c x1 x2 x3 y1 y2 y3 : ℝ)
    (hsc : s ^ 2 + c ^ 2 = 1)
    (hx : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1)
    (hy : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 1) :
    (s * (x1 * y1 - x2 * y2)) ^ 2 +
    (-s * (x1 * y2 + x2 * y1)) ^ 2 +
    (c * x3 * y3) ^ 2 ≤ 1 := by
  have h_alg : (s * (x1 * y1 - x2 * y2)) ^ 2 +
      (-s * (x1 * y2 + x2 * y1)) ^ 2 +
      (c * x3 * y3) ^ 2 =
      s ^ 2 * (x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2) + c ^ 2 * x3 ^ 2 * y3 ^ 2 := by ring
  rw [h_alg]
  set a := x1 ^ 2 + x2 ^ 2
  set b := y1 ^ 2 + y2 ^ 2
  have hS0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hC0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hx1 : 0 ≤ x1 ^ 2 := sq_nonneg x1
  have hx2 : 0 ≤ x2 ^ 2 := sq_nonneg x2
  have hx3 : 0 ≤ x3 ^ 2 := sq_nonneg x3
  have hy1 : 0 ≤ y1 ^ 2 := sq_nonneg y1
  have hy2 : 0 ≤ y2 ^ 2 := sq_nonneg y2
  have hy3 : 0 ≤ y3 ^ 2 := sq_nonneg y3
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have hx3_eq : x3 ^ 2 = 1 - a := by linarith
  have hy3_eq : y3 ^ 2 = 1 - b := by linarith
  rw [hx3_eq, hy3_eq]
  have hab1 : a * b ≤ 1 := by nlinarith
  have hab2 : (1 - a) * (1 - b) ≤ 1 := by nlinarith
  nlinarith

lemma ghz_closed_network_lambda_le_two_pauli_coeff_prop (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (k : Fin 4) :
    (ghz_pauli_coeff M k 0 = 1 ∧ ghz_pauli_coeff M k 1 = 0 ∧ ghz_pauli_coeff M k 2 = 0 ∧ ghz_pauli_coeff M k 3 = 0) ∨
    (ghz_pauli_coeff M k 0 = 0 ∧
     (ghz_pauli_coeff M k 1)^2 + (ghz_pauli_coeff M k 2)^2 + (ghz_pauli_coeff M k 3)^2 = 1) := by
  have row_norm : ∀ i : Fin 3, (M i 0)^2 + (M i 1)^2 + (M i 2)^2 = 1 := by
    intro i
    rw [Matrix.mem_orthogonalGroup_iff] at hM
    have h := congr_fun (congr_fun hM i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, Fin.sum_univ_three] at h
    linarith [h]
  fin_cases k
  · left; dsimp [ghz_pauli_coeff]; exact ⟨rfl, rfl, rfl, rfl⟩
  · right; dsimp [ghz_pauli_coeff]; exact ⟨rfl, row_norm 0⟩
  · right; dsimp [ghz_pauli_coeff]; exact ⟨rfl, row_norm 1⟩
  · right; dsimp [ghz_pauli_coeff]; exact ⟨rfl, row_norm 2⟩

lemma ghz_closed_network_lambda_le_two_norm_sq_le_one (α : ℝ) (e f : Matrix (Fin 3) (Fin 3) ℝ)
    (he : e ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hf : f ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (μ ν : Fin 4) :
    ghz_correlation_vector α e f μ ν ⬝ᵥ ghz_correlation_vector α e f μ ν ≤ 1 := by
  have h_dot : ghz_correlation_vector α e f μ ν ⬝ᵥ ghz_correlation_vector α e f μ ν =
      (Real.sin (2 * α) * (ghz_pauli_coeff e μ 1 * ghz_pauli_coeff f ν 1 - ghz_pauli_coeff e μ 2 * ghz_pauli_coeff f ν 2)) ^ 2 +
      (- Real.sin (2 * α) * (ghz_pauli_coeff e μ 1 * ghz_pauli_coeff f ν 2 + ghz_pauli_coeff e μ 2 * ghz_pauli_coeff f ν 1)) ^ 2 +
      (Real.cos (2 * α) * ghz_pauli_coeff e μ 0 * ghz_pauli_coeff f ν 0 +
       ghz_pauli_coeff e μ 0 * ghz_pauli_coeff f ν 3 +
       ghz_pauli_coeff e μ 3 * ghz_pauli_coeff f ν 0 +
       Real.cos (2 * α) * ghz_pauli_coeff e μ 3 * ghz_pauli_coeff f ν 3) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three, sq]
    dsimp [ghz_correlation_vector]
  rw [h_dot]
  rcases ghz_closed_network_lambda_le_two_pauli_coeff_prop e he μ with ⟨ae0, ae1, ae2, ae3⟩ | ⟨ae0, he_sum⟩
  · rcases ghz_closed_network_lambda_le_two_pauli_coeff_prop f hf ν with ⟨cf0, cf1, cf2, cf3⟩ | ⟨cf0, hf_sum⟩
    · rw [ae0, ae1, ae2, ae3, cf0, cf1, cf2, cf3]
      have hcos : (Real.cos (2 * α)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * α)
      nlinarith
    · rw [ae0, ae1, ae2, ae3, cf0]
      have h1 : 0 ≤ (ghz_pauli_coeff f ν 1) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (ghz_pauli_coeff f ν 2) ^ 2 := sq_nonneg _
      nlinarith
  · rcases ghz_closed_network_lambda_le_two_pauli_coeff_prop f hf ν with ⟨cf0, cf1, cf2, cf3⟩ | ⟨cf0, hf_sum⟩
    · rw [ae0, cf0, cf1, cf2, cf3]
      have h1 : 0 ≤ (ghz_pauli_coeff e μ 1) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (ghz_pauli_coeff e μ 2) ^ 2 := sq_nonneg _
      nlinarith
    · rw [ae0, cf0]
      have h_simp : (Real.cos (2 * α) * 0 * 0 +
          0 * ghz_pauli_coeff f ν 3 +
          ghz_pauli_coeff e μ 3 * 0 +
          Real.cos (2 * α) * ghz_pauli_coeff e μ 3 * ghz_pauli_coeff f ν 3) =
          Real.cos (2 * α) * ghz_pauli_coeff e μ 3 * ghz_pauli_coeff f ν 3 := by ring
      rw [h_simp]
      exact ghz_closed_network_lambda_le_two_norm_sq_bound (Real.sin (2 * α)) (Real.cos (2 * α)) _ _ _ _ _ _
        (Real.sin_sq_add_cos_sq (2 * α)) he_sum hf_sum

/-- Universal upper bound Lambda(tau_{mu nu}, tau_{mu' nu'}) <= 2 for all alpha, orthonormal frames, and setting quadruples. -/
theorem ghz_closed_network_lambda_le_two (α : ℝ) (e f : Matrix (Fin 3) (Fin 3) ℝ) (he : e ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hf : f ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (μ ν μ' ν' : Fin 4) :
    bell_network_lambda (ghz_correlation_vector α e f μ ν) (ghz_correlation_vector α e f μ' ν') ≤ 2 := by
  have hu : ghz_correlation_vector α e f μ ν ⬝ᵥ ghz_correlation_vector α e f μ ν ≤ 1 :=
    ghz_closed_network_lambda_le_two_norm_sq_le_one α e f he hf μ ν
  have hv : ghz_correlation_vector α e f μ' ν' ⬝ᵥ ghz_correlation_vector α e f μ' ν' ≤ 1 :=
    ghz_closed_network_lambda_le_two_norm_sq_le_one α e f he hf μ' ν'
  have h_le := ghz_standard_frame_lambda_le_lambda_le_s
    (ghz_correlation_vector α e f μ ν) (ghz_correlation_vector α e f μ' ν')
  linarith
