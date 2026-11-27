import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsSeparable

/-!
# matrix_is_separable_pos_semidef

Topic: quantum   Node: e618f9064088

Provenance: helper lemma. Helper for OP-2466: a separable operator is positive semidefinite (with matrix_is_separable_partial_transpose_iff, separable implies PPT).

Every separable bipartite matrix (matrix_is_separable dA dB ρ) is positive semidefinite.
-/

theorem matrix_is_separable_pos_semidef (dA dB : ℕ)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (h : matrix_is_separable dA dB ρ) :
    open scoped ComplexOrder in ρ.PosSemidef := by
  open scoped ComplexOrder in
  obtain ⟨N, x, y, h⟩ := h
  have hρ : ρ = ∑ i : Fin N, Matrix.vecMulVec (fun p : Fin dA × Fin dB => x i p.1 * y i p.2)
      (star fun p : Fin dA × Fin dB => x i p.1 * y i p.2) := by
    ext p q
    rw [h p q, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_mul']
    ring
  rw [hρ]
  exact Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_vecMulVec_self_star _
