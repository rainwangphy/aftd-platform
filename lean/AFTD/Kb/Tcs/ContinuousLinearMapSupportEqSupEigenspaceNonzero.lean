import AFTD.Prelude

/-!
# ContinuousLinearMap.support_eq_sup_eigenspace_nonzero

Topic: quantum   Node: e311bd6c0945

Provenance: formalization of a published result. Source: QuantumInfo, `ContinuousLinearMap.support_eq_sup_eigenspace_nonzero`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousLinearMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The support of a Hermitian matrix is the sum of its nonzero eigenspaces.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] in
/-- The support of a Hermitian matrix is the sum of its nonzero eigenspaces. -/
theorem ContinuousLinearMap.support_eq_sup_eigenspace_nonzero (A : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)
    (hA : A.IsSymmetric) : A.range = ⨆ μ ≠ 0, Module.End.eigenspace A μ := by
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    have h_decomp : y ∈ ⨆ (μ : 𝕜), Module.End.eigenspace A.toLinearMap μ := by
      have h_orth := hA.orthogonalComplement_iSup_eigenspaces_eq_bot
      rw [Submodule.orthogonal_eq_bot_iff] at h_orth
      rw [h_orth]
      exact Submodule.mem_top;
    rw [Submodule.mem_iSup_iff_exists_finsupp] at h_decomp
    rcases h_decomp with ⟨f, hf₁, hf₂⟩
    have h_apply_A : A y = ∑ i ∈ f.support, A (f i) := by
      rw [← hf₂, map_finsuppSum]
      exact rfl
    have h_eigen (i) : A (f i) = (i : 𝕜) • f i :=
      Module.End.mem_eigenspace_iff.mp (hf₁ i)
    rw [← hy, coe_coe, h_apply_A, Finset.sum_congr rfl (fun i _ ↦ h_eigen i)]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi0 : i = 0
    · simp [hi0]
    · apply Submodule.smul_mem
      apply Submodule.mem_iSup_of_mem i
      exact Submodule.mem_iSup_of_mem hi0 (hf₁ i)
  · simp only [iSup_le_iff]
    intro μ hμ x hx
    use μ⁻¹ • x
    simp_all
