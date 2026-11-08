import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixCutNorm

/-!
# matrix_cut_norm_zero

Topic: graphs   Node: df6671ec9d5d

Provenance: helper lemma. arXiv:2611.05048 Section 1

The cut norm of the all-zero matrix is zero.
-/

/-- The cut norm of the all-zero matrix is zero. -/
theorem matrix_cut_norm_zero {α β : Type*} [Fintype α] [Fintype β] :
    matrix_cut_norm (fun (_ : α) (_ : β) => (0 : ℝ)) = 0 := by
  unfold matrix_cut_norm
  simp
