import AFTD.Prelude

/-!
# quantum_projection_expectation_norm_sq

Topic: quantum_mechanics   Node: e84b06fe5eff

For any orthogonal projection operator P (a self-adjoint idempotent continuous linear map) on a complex Hilbert space E and any state vector ψ in E, the inner product ⟪ψ, P ψ⟫_ℂ equals the complex square of the norm ‖P ψ‖.
-/

/-- The expectation value of an orthogonal projection operator equals the squared norm of the projected state. -/
theorem quantum_projection_expectation_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] E) (hP : IsStarProjection P) (ψ : E) :
    inner ℂ ψ (P ψ) = (‖P ψ‖ : ℂ) ^ 2 := by
  have h_adj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hP.isSelfAdjoint.star_eq
  have h_idem : P (P ψ) = P ψ := congr_arg (· ψ) hP.isIdempotentElem
  nth_rw 1 [← h_idem]
  rw [← ContinuousLinearMap.adjoint_inner_left, h_adj]
  exact inner_self_eq_norm_sq_to_K (P ψ)
