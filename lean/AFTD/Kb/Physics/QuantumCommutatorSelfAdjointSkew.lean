import AFTD.Prelude

/-!
# quantum_commutator_self_adjoint_skew

Topic: quantum_mechanics   Node: 0295a568568c

The commutator [A, B] = A * B - B * A of two self-adjoint continuous linear operators A and B on a complex Hilbert space is skew-adjoint, that is, star ⁅A, B⁆ = -⁅A, B⁆.
-/

/-- The commutator of two self-adjoint operators is skew-adjoint (anti-self-adjoint). -/
theorem quantum_commutator_self_adjoint_skew {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    star ⁅A, B⁆ = -⁅A, B⁆ := by
  simp only [Ring.lie_def, star_sub, star_mul, hA.star_eq, hB.star_eq]
  abel
