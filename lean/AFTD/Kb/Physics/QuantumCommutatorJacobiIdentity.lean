import AFTD.Prelude

/-!
# quantum_commutator_jacobi_identity

Topic: quantum_mechanics   Node: f5fdb46c69b0

Provenance: formalization of a published result. Source: Hall, Quantum Theory for Mathematicians, Chapter 3; Reed & Simon, Methods of Modern Mathematical Physics I, ch. VIII

For any three continuous linear operators A, B, C on a complex inner product space E, their commutators satisfy the Jacobi identity: ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0.
-/

/-- The commutator bracket on continuous linear operators satisfies the Jacobi identity. -/
theorem quantum_commutator_jacobi_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B C : E →L[ℂ] E) :
    ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 := by
  simp only [Ring.lie_def]
  noncomm_ring
