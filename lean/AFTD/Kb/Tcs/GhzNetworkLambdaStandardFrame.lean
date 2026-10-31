import AFTD.Prelude
import AFTD.Kb.Tcs.BellNetworkLambda
import AFTD.Kb.Tcs.GhzCorrelationVector
import AFTD.Kb.Tcs.GhzPauliCoeff

/-!
# ghz_network_lambda_standard_frame

Topic: quantum   Node: 32611ea4344c

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. III.4

For the generalized GHZ state with parameter alpha, the identity frames e = I and f = I at indices (3, 0) and (1, 1) satisfy Lambda(tau_{30}, tau_{11}) = 1 + sin^2(2*alpha).
-/

lemma ghz_network_lambda_standard_frame_u_dot_u (α : ℝ) :
    (ghz_correlation_vector α 1 1 3 0 ⬝ᵥ ghz_correlation_vector α 1 1 3 0) = 1 := by
  simp only [dotProduct, Fin.sum_univ_three]
  dsimp [ghz_correlation_vector, ghz_pauli_coeff]
  simp

lemma ghz_network_lambda_standard_frame_v_dot_v (α : ℝ) :
    (ghz_correlation_vector α 1 1 1 1 ⬝ᵥ ghz_correlation_vector α 1 1 1 1) = Real.sin (2 * α) ^ 2 := by
  simp only [dotProduct, Fin.sum_univ_three]
  dsimp [ghz_correlation_vector, ghz_pauli_coeff]
  simp [sq]

lemma ghz_network_lambda_standard_frame_u_dot_v (α : ℝ) :
    (ghz_correlation_vector α 1 1 3 0 ⬝ᵥ ghz_correlation_vector α 1 1 1 1) = 0 := by
  simp only [dotProduct, Fin.sum_univ_three]
  dsimp [ghz_correlation_vector, ghz_pauli_coeff]
  simp

/-- The standard frame evaluation of Lambda(tau_{30}, tau_{11}) equals 1 + sin^2(2*alpha). -/
theorem ghz_network_lambda_standard_frame (α : ℝ) : bell_network_lambda (ghz_correlation_vector α 1 1 3 0) (ghz_correlation_vector α 1 1 1 1) = 1 + Real.sin (2 * α) ^ 2 := by
  set u := ghz_correlation_vector α 1 1 3 0
  set v := ghz_correlation_vector α 1 1 1 1
  change (1 / 2 : ℝ) * ((u ⬝ᵥ u + v ⬝ᵥ v) + Real.sqrt ((u ⬝ᵥ u + v ⬝ᵥ v) ^ 2 - 4 * (u ⬝ᵥ v) ^ 2)) =
    1 + Real.sin (2 * α) ^ 2
  have hu : u ⬝ᵥ u = 1 := ghz_network_lambda_standard_frame_u_dot_u α
  have hv : v ⬝ᵥ v = Real.sin (2 * α) ^ 2 := ghz_network_lambda_standard_frame_v_dot_v α
  have huv : u ⬝ᵥ v = 0 := ghz_network_lambda_standard_frame_u_dot_v α
  rw [hu, hv, huv]
  have hpos : 0 ≤ 1 + Real.sin (2 * α) ^ 2 := by positivity
  have hsq : Real.sqrt ((1 + Real.sin (2 * α) ^ 2) ^ 2 - 4 * (0 : ℝ) ^ 2) = 1 + Real.sin (2 * α) ^ 2 := by
    have : 4 * (0 : ℝ) ^ 2 = 0 := by ring
    rw [this, sub_zero, Real.sqrt_sq hpos]
  rw [hsq]
  ring
