import AFTD.Prelude

/-!
# anticommuting_hermitian_expectation_sq_le_one

Topic: quantum   Node: 6d420740553d

Provenance: formalization of a published result. Source: arXiv:2610.35838 Appendix E, Fact 1

If continuous linear operators P and Q on a complex Hilbert space are self-adjoint, have operator norm at most one, and anticommute (P * Q + Q * P = 0), then for any unit vector psi, the sum of the squares of the real expectation values satisfies (re <psi, P psi>)^2 + (re <psi, Q psi>)^2 <= 1.
-/

/-- Fact 1: Anticommuting Hermitian operators with norm <= 1 satisfy <P>^2 + <Q>^2 <= 1 in any quantum state. -/
theorem anticommuting_hermitian_expectation_sq_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P Q : E →L[ℂ] E) (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hP_norm : ‖P‖ ≤ 1) (hQ_norm : ‖Q‖ ≤ 1)
    (h_anticomm : P * Q + Q * P = 0)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    (RCLike.re (inner ℂ ψ (P ψ))) ^ 2 + (RCLike.re (inner ℂ ψ (Q ψ))) ^ 2 ≤ 1 := by
  set a := RCLike.re (inner ℂ ψ (P ψ))
  set b := RCLike.re (inner ℂ ψ (Q ψ))
  set v := (a : ℂ) • (P ψ) + (b : ℂ) • (Q ψ)
  have h_ortho : RCLike.re (inner ℂ (P ψ) (Q ψ)) = 0 := by
    have h1 : inner ℂ (P ψ) (Q ψ) = inner ℂ ψ (P (Q ψ)) := by
      have h := ContinuousLinearMap.adjoint_inner_right P ψ (Q ψ)
      rw [← ContinuousLinearMap.star_eq_adjoint, hP] at h
      exact h.symm
    have h2 : inner ℂ (Q ψ) (P ψ) = inner ℂ ψ (Q (P ψ)) := by
      have h := ContinuousLinearMap.adjoint_inner_right Q ψ (P ψ)
      rw [← ContinuousLinearMap.star_eq_adjoint, hQ] at h
      exact h.symm
    have h3 : starRingEnd ℂ (inner ℂ (P ψ) (Q ψ)) = inner ℂ (Q ψ) (P ψ) :=
      inner_conj_symm (Q ψ) (P ψ)
    have h4 : inner ℂ (P ψ) (Q ψ) + starRingEnd ℂ (inner ℂ (P ψ) (Q ψ)) = 0 := by
      rw [h3, h1, h2, ← inner_add_right]
      change inner ℂ ψ ((P * Q + Q * P) ψ) = 0
      rw [h_anticomm]
      exact inner_zero_right ψ
    have h5 := (RCLike.add_conj (inner ℂ (P ψ) (Q ψ))).symm.trans h4
    have h6 : (RCLike.re (inner ℂ (P ψ) (Q ψ)) : ℂ) = 0 := by
      cases mul_eq_zero.mp h5 with
      | inl h7 => norm_num at h7
      | inr h7 => exact h7
    exact Complex.ofReal_eq_zero.mp h6

  have h_norm_sq : ‖v‖ ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ)]
    have h_cross : RCLike.re (inner ℂ ((a : ℂ) • (P ψ)) ((b : ℂ) • (Q ψ))) = 0 := by
      calc RCLike.re (inner ℂ ((a : ℂ) • (P ψ)) ((b : ℂ) • (Q ψ)))
        _ = a * b * RCLike.re (inner ℂ (P ψ) (Q ψ)) := by simp; ring
        _ = 0 := by rw [h_ortho, mul_zero]
    have hP_le : ‖P ψ‖ ≤ 1 := by
      have h := P.le_opNorm ψ
      have : ‖P‖ * ‖ψ‖ ≤ 1 * 1 := by rw [hψ]; exact mul_le_mul_of_nonneg_right hP_norm zero_le_one
      linarith
    have hQ_le : ‖Q ψ‖ ≤ 1 := by
      have h := Q.le_opNorm ψ
      have : ‖Q‖ * ‖ψ‖ ≤ 1 * 1 := by rw [hψ]; exact mul_le_mul_of_nonneg_right hQ_norm zero_le_one
      linarith
    have hP_sq : ‖(a : ℂ) • (P ψ)‖ ^ 2 ≤ a ^ 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      have : ‖P ψ‖ ^ 2 ≤ 1 := by
        have : 0 ≤ ‖P ψ‖ := norm_nonneg _
        nlinarith
      nlinarith
    have hQ_sq : ‖(b : ℂ) • (Q ψ)‖ ^ 2 ≤ b ^ 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      have : ‖Q ψ‖ ^ 2 ≤ 1 := by
        have : 0 ≤ ‖Q ψ‖ := norm_nonneg _
        nlinarith
      nlinarith
    linarith

  have h_inner : RCLike.re (inner ℂ ψ v) = a ^ 2 + b ^ 2 := by
    simp only [v, inner_add_right, inner_smul_right, map_add]
    have ha : RCLike.re ((a : ℂ) * inner ℂ ψ (P ψ)) = a ^ 2 := by
      have h : RCLike.re ((a : ℂ) * inner ℂ ψ (P ψ)) = a * RCLike.re (inner ℂ ψ (P ψ)) := by simp
      rw [h, sq]
    have hb : RCLike.re ((b : ℂ) * inner ℂ ψ (Q ψ)) = b ^ 2 := by
      have h : RCLike.re ((b : ℂ) * inner ℂ ψ (Q ψ)) = b * RCLike.re (inner ℂ ψ (Q ψ)) := by simp
      rw [h, sq]
    rw [ha, hb]

  have h_cs : a ^ 2 + b ^ 2 ≤ ‖v‖ := by
    rw [← h_inner]
    calc RCLike.re (inner ℂ ψ v)
      _ ≤ ‖inner ℂ ψ v‖ := RCLike.re_le_norm _
      _ ≤ ‖ψ‖ * ‖v‖ := norm_inner_le_norm _ _
      _ = ‖v‖ := by rw [hψ, one_mul]

  have h_sq_le : (a ^ 2 + b ^ 2) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have hpos : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    have h1 : (a ^ 2 + b ^ 2) ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith
    linarith

  have h_final : a ^ 2 + b ^ 2 ≤ 1 := by nlinarith
  exact h_final
