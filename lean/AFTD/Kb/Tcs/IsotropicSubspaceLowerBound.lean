import AFTD.Prelude

/-!
# isotropic_subspace_lower_bound

Topic: quantum   Node: 8c6d51252214

Provenance: helper lemma. step towards line_cubic_t_count_lower_bound

If V is an isotropic subspace of (M → ZMod 2) under the standard dot product, the all-ones vector is orthogonal to V, and the all-ones vector is not in V, then 2 * finrank V + 1 ≤ card M.
-/

/-- If V is an isotropic subspace of (M → ZMod 2), the all-ones vector is orthogonal to V, and the all-ones vector is not in V, then 2 * finrank V + 1 ≤ card M. -/
theorem isotropic_subspace_lower_bound {M : Type*} [Fintype M]
    (V : Submodule (ZMod 2) (M → ZMod 2))
    (h_iso : ∀ u ∈ V, ∀ v ∈ V, (∑ m, u m * v m) = 0)
    (h_ones_ortho : ∀ v ∈ V, ∑ m, v m = 0)
    (h_ones_notin : (fun _ : M => (1 : ZMod 2)) ∉ V) :
    2 * Module.finrank (ZMod 2) V + 1 ≤ Fintype.card M := by
  open Matrix LinearMap in
  classical
  let B : LinearMap.BilinForm (ZMod 2) (M → ZMod 2) := toBilin' (1 : Matrix M M (ZMod 2))
  have hB_nondeg : B.Nondegenerate := by
    apply Matrix.Nondegenerate.toBilin'
    rw [nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero]
    simp
  have h_le_ortho : V ≤ B.orthogonal V := by
    intro v hv
    rw [BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [toBilin'_apply']
    simp only [one_mulVec, dotProduct]
    exact h_iso u hu v hv
  have h_rank_ortho : Module.finrank (ZMod 2) (B.orthogonal V) =
      Fintype.card M - Module.finrank (ZMod 2) V := by
    rw [BilinForm.finrank_orthogonal hB_nondeg, Module.finrank_pi]
  have h_le_card : Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) (B.orthogonal V) :=
    Submodule.finrank_mono h_le_ortho
  have h_ones_in_ortho : (fun _ : M => (1 : ZMod 2)) ∈ B.orthogonal V := by
    rw [BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [toBilin'_apply']
    simp only [one_mulVec, dotProduct, mul_one]
    exact h_ones_ortho u hu
  have h_two_rank_le : 2 * Module.finrank (ZMod 2) V ≤ Fintype.card M := by
    omega
  have h_ne : 2 * Module.finrank (ZMod 2) V ≠ Fintype.card M := by
    intro h_eq
    have h_ranks_eq : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (B.orthogonal V) := by
      omega
    have h_V_eq : V = B.orthogonal V := Submodule.eq_of_le_of_finrank_eq h_le_ortho h_ranks_eq
    have : (fun _ : M => (1 : ZMod 2)) ∈ V := by
      rw [h_V_eq]
      exact h_ones_in_ortho
    exact h_ones_notin this
  omega
