import AFTD.Prelude
import AFTD.Kb.Tcs.BellNetworkLambda
import AFTD.Kb.Tcs.GhzCorrelationVector
import AFTD.Kb.Tcs.GhzPauliCoeff

/-!
# ghz_standard_frame_lambda_le

Topic: quantum   Node: e32da3b5b313

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 15

For the generalized GHZ state with parameter alpha and standard identity frames e = 1 and f = 1, the two-copy closed-network quantity Lambda(tau_{mu nu}, tau_{mu' nu'}) is at most 1 + sin^2(2*alpha) for all setting indices mu, nu, mu', nu' in {0, 1, 2, 3}.
-/

lemma ghz_standard_frame_lambda_le_dot_self_nonneg (u : Fin 3 → ℝ) : 0 ≤ u ⬝ᵥ u := by
  change 0 ≤ ∑ i : Fin 3, u i * u i
  apply Finset.sum_nonneg
  intro i _
  nlinarith

lemma ghz_standard_frame_lambda_le_lambda_le_s (u v : Fin 3 → ℝ) : bell_network_lambda u v ≤ (u ⬝ᵥ u) + (v ⬝ᵥ v) := by
  dsimp [bell_network_lambda]
  set s := (u ⬝ᵥ u) + (v ⬝ᵥ v)
  have hs : 0 ≤ s := add_nonneg (ghz_standard_frame_lambda_le_dot_self_nonneg u) (ghz_standard_frame_lambda_le_dot_self_nonneg v)
  have hdisc_le : s ^ 2 - 4 * (u ⬝ᵥ v) ^ 2 ≤ s ^ 2 := by nlinarith
  have hsqrt_le : Real.sqrt (s ^ 2 - 4 * (u ⬝ᵥ v) ^ 2) ≤ s := by
    calc
      Real.sqrt (s ^ 2 - 4 * (u ⬝ᵥ v) ^ 2) ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hdisc_le
      _ = s := Real.sqrt_sq hs
  linarith

lemma ghz_standard_frame_lambda_le_z_axis_dot (u v : Fin 3 → ℝ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    u ⬝ᵥ v = u 2 * v 2 := by
  simp only [dotProduct, Fin.sum_univ_three]
  rw [hu0, hu1, hv0, hv1]
  ring

lemma ghz_standard_frame_lambda_le_lambda_z_axis (u v : Fin 3 → ℝ) (hu0 : u 0 = 0) (hu1 : u 1 = 0) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    bell_network_lambda u v ≤ max (u ⬝ᵥ u) (v ⬝ᵥ v) := by
  have hu : u ⬝ᵥ u = (u 2) ^ 2 := by
    have := ghz_standard_frame_lambda_le_z_axis_dot u u hu0 hu1 hu0 hu1
    linarith [this]
  have hv : v ⬝ᵥ v = (v 2) ^ 2 := by
    have := ghz_standard_frame_lambda_le_z_axis_dot v v hv0 hv1 hv0 hv1
    linarith [this]
  have huv : u ⬝ᵥ v = u 2 * v 2 := ghz_standard_frame_lambda_le_z_axis_dot u v hu0 hu1 hv0 hv1
  dsimp [bell_network_lambda]
  rw [hu, hv, huv]
  set a := (u 2) ^ 2
  set b := (v 2) ^ 2
  have hdisc : (a + b) ^ 2 - 4 * (u 2 * v 2) ^ 2 = (a - b) ^ 2 := by
    dsimp [a, b]
    ring
  rw [hdisc, Real.sqrt_sq_eq_abs]
  cases le_total a b with
  | inl h =>
    have habs : |a - b| = b - a := abs_sub_comm a b ▸ abs_of_nonneg (sub_nonneg.mpr h)
    rw [habs]
    have : (1 / 2 : ℝ) * (a + b + (b - a)) = b := by ring
    rw [this]
    exact le_max_right a b
  | inr h =>
    have habs : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr h)
    rw [habs]
    have : (1 / 2 : ℝ) * (a + b + (a - b)) = a := by ring
    rw [this]
    exact le_max_left a b

lemma ghz_standard_frame_lambda_le_u_dot_u_le_one (α : ℝ) (μ ν : Fin 4) :
    ghz_correlation_vector α 1 1 μ ν ⬝ᵥ ghz_correlation_vector α 1 1 μ ν ≤ 1 := by
  simp only [dotProduct, Fin.sum_univ_three]
  dsimp [ghz_correlation_vector, ghz_pauli_coeff]
  fin_cases μ <;> fin_cases ν <;> (
    simp [Matrix.one_apply]
    try nlinarith [Real.sin_sq_add_cos_sq (2 * α)]
  )

lemma ghz_standard_frame_lambda_le_cases (α : ℝ) (μ ν : Fin 4) :
    ((ghz_correlation_vector α 1 1 μ ν) 0 = 0 ∧ (ghz_correlation_vector α 1 1 μ ν) 1 = 0) ∨
    (ghz_correlation_vector α 1 1 μ ν ⬝ᵥ ghz_correlation_vector α 1 1 μ ν ≤ Real.sin (2 * α) ^ 2) := by
  dsimp [ghz_correlation_vector, ghz_pauli_coeff]
  simp only [dotProduct, Fin.sum_univ_three]
  fin_cases μ <;> fin_cases ν <;> (
    simp [Matrix.one_apply, sq]
    try nlinarith
  )

/-- For standard identity frames e = I and f = I, the two-copy closed-network quantity Lambda is at most 1 + sin^2(2*alpha) for all setting quadruples. -/
theorem ghz_standard_frame_lambda_le (α : ℝ) (μ ν μ' ν' : Fin 4) :
    bell_network_lambda (ghz_correlation_vector α 1 1 μ ν) (ghz_correlation_vector α 1 1 μ' ν') ≤ 1 + Real.sin (2 * α) ^ 2 := by
  set u := ghz_correlation_vector α 1 1 μ ν
  set v := ghz_correlation_vector α 1 1 μ' ν'
  have hu_le_1 : u ⬝ᵥ u ≤ 1 := ghz_standard_frame_lambda_le_u_dot_u_le_one α μ ν
  have hv_le_1 : v ⬝ᵥ v ≤ 1 := ghz_standard_frame_lambda_le_u_dot_u_le_one α μ' ν'
  rcases ghz_standard_frame_lambda_le_cases α μ ν with ⟨hu0, hu1⟩ | hu_sin
  · rcases ghz_standard_frame_lambda_le_cases α μ' ν' with ⟨hv0, hv1⟩ | hv_sin
    · have h_z := ghz_standard_frame_lambda_le_lambda_z_axis u v hu0 hu1 hv0 hv1
      have hmax : max (u ⬝ᵥ u) (v ⬝ᵥ v) ≤ 1 := max_le hu_le_1 hv_le_1
      have hsin_ge : 0 ≤ Real.sin (2 * α) ^ 2 := sq_nonneg _
      linarith
    · have h_s := ghz_standard_frame_lambda_le_lambda_le_s u v
      linarith
  · have h_s := ghz_standard_frame_lambda_le_lambda_le_s u v
    linarith
