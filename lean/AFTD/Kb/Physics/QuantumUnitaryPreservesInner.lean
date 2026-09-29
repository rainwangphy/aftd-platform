import AFTD.Prelude

/-!
# quantum_unitary_preserves_inner

Topic: quantum_mechanics   Node: 5cd473a0ebf8

For any unitary continuous linear operator U on a complex Hilbert space E and any vectors ϕ and ψ in E, the inner product is preserved: ⟪U ϕ, U ψ⟫_ℂ = ⟪ϕ, ψ⟫_ℂ.
-/

/-- A unitary operator preserves the complex inner product between states. -/
theorem quantum_unitary_preserves_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) (ϕ ψ : E) :
    inner ℂ (U ϕ) (U ψ) = inner ℂ ϕ ψ := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ ϕ ((star U * U) ψ) = inner ℂ ϕ ψ
  rw [hU.1]
  rfl
