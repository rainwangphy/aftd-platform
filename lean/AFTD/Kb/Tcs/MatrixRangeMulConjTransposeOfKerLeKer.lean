import AFTD.Prelude

/-!
# Matrix.range_mul_conjTranspose_of_ker_le_ker

Topic: quantum   Node: 0be7e2439f2c

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.range_mul_conjTranspose_of_ker_le_ker`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If ker M ⊆ ker A, then range (A Mᴴ) = range A.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] in
/-- If ker M ⊆ ker A, then range (A Mᴴ) = range A. -/
theorem Matrix.range_mul_conjTranspose_of_ker_le_ker {A : Matrix d d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ LinearMap.ker A.toEuclideanLin) :
    LinearMap.range (A * M.conjTranspose).toEuclideanLin = LinearMap.range A.toEuclideanLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    use (M.conjTranspose.toEuclideanLin) y;
    simp [Matrix.toEuclideanLin]
  · intro x hx;
    -- Since $x \in \text{range}(A)$, there exists $y \in \text{range}(Mᴴ)$ such that $A y = x$.
    obtain ⟨y, hy⟩ : ∃ y ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), A.toEuclideanLin y = x := by
      have h_range_MH : LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) = (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
        have h_orthogonal : (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)))ᗮ = LinearMap.ker (Matrix.toEuclideanLin M) := by
          ext x
          rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
          simp only [Submodule.mem_orthogonal, LinearMap.mem_ker, LinearMap.mem_range]
          constructor
          · intro h
            rw [← inner_self_eq_zero (𝕜 := 𝕜)]
            have : ∀ y, @inner 𝕜 _ _ y (Matrix.toEuclideanLin M x) = 0 := by
              intro y
              rw [← LinearMap.adjoint_inner_left]
              exact h _ ⟨y, rfl⟩
            exact this _
          · intro h y ⟨z, hz⟩
            rw [← hz, LinearMap.adjoint_inner_left, h, inner_zero_right]
        rw [← h_orthogonal, Submodule.orthogonal_orthogonal]
      obtain ⟨ y, rfl ⟩ := hx;
      -- Since $y$ is in the range of $Mᴴ$, we can write $y$ as $y = y_1 + y_2$ where $y_1 \in \text{range}(Mᴴ)$ and $y_2 \in \text{ker}(M)$.
      obtain ⟨y1, y2, hy1, hy2, hy⟩ : ∃ y1 y2 : EuclideanSpace 𝕜 d, y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) ∧ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M) ∧ y = y1 + y2 := by
        have h_decomp : ∀ y : EuclideanSpace 𝕜 d, ∃ y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), ∃ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M), y = y1 + y2 := by
          intro y
          have h_decomp : y ∈ (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose))) ⊔ (LinearMap.ker (Matrix.toEuclideanLin M)) := by
            rw [ h_range_MH ];
            rw [ sup_comm, Submodule.sup_orthogonal_of_hasOrthogonalProjection ];
            exact Submodule.mem_top;
          rw [ Submodule.mem_sup ] at h_decomp ; tauto;
        exact ⟨ _, _, h_decomp y |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.right ⟩;
      exact ⟨ y1, hy1, by rw [ hy, map_add, LinearMap.mem_ker.mp ( h hy2 ) ] ; simp ⟩;
    obtain ⟨ z, rfl ⟩ := hy.1;
    exact ⟨ z, by simpa [ Matrix.toEuclideanLin ] using hy.2 ⟩
