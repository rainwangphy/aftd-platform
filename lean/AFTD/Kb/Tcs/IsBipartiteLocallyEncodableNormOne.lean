import AFTD.Prelude
import AFTD.Kb.Tcs.IsBipartiteLocallyEncodable

/-!
# is_bipartite_locally_encodable_norm_one

Topic: quantum   Node: 5bd457b5bb40

Provenance: formalization of a published result. Source: arXiv:2611.16921 Sec. II.1

For nonempty finite types m and n, every locally encodable state ψ in EuclideanSpace ℂ (m × n) satisfies ‖ψ‖ = 1.
-/

/-- Any locally encodable bipartite state in a nonempty system has norm 1. -/
theorem is_bipartite_locally_encodable_norm_one {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n]
    {ψ : EuclideanSpace ℂ (m × n)} (h : is_bipartite_locally_encodable ψ) :
    ‖ψ‖ = 1 := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨j⟩ := (inferInstance : Nonempty (m × n))
  obtain ⟨uA, uB, hBj⟩ := hB j
  -- the local unitary `uA ⊗ₖ uB` is unitary
  set M : Matrix (m × n) (m × n) ℂ := Matrix.kronecker (uA : Matrix m m ℂ) (uB : Matrix n n ℂ)
    with hM
  have hmem : M ∈ Matrix.unitaryGroup (m × n) ℂ := Matrix.kronecker_mem_unitary uA.2 uB.2
  have hstar : star (Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) M)
      = Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (star M) :=
    ((Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ)).map_star' M).symm
  have hmul : ∀ A B : Matrix (m × n) (m × n) ℂ,
      Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) A *
          Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) B
        = Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (A * B) :=
    fun A B => ((Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ)).map_mul A B).symm
  have hone : Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (1 : Matrix (m × n) (m × n) ℂ)
      = 1 :=
    (Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ)).map_one
  -- hence the induced operator on `EuclideanSpace ℂ (m × n)` is unitary, so it is an isometry
  have hU : Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) M ∈
      unitary (EuclideanSpace ℂ (m × n) →L[ℂ] EuclideanSpace ℂ (m × n)) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [hstar, hmul, hmem.1, hone]
    · rw [hstar, hmul, hmem.2, hone]
  have hnorm : ‖(Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) M) ψ‖ = ‖ψ‖ :=
    ContinuousLinearMap.norm_map_of_mem_unitary hU ψ
  have happ : (Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) M) ψ = B j := by
    rw [hBj]
    exact congrArg (fun f => f ψ) (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M)
  rw [← hnorm, happ]
  exact B.orthonormal.1 j
