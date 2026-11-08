import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonPiOrd
import AFTD.Kb.Tcs.ComparisonTriangleKappaMemEvalKer
import AFTD.Kb.Tcs.ComparisonEvalMatrix
import AFTD.Kb.Tcs.ComparisonPhi2
import AFTD.Kb.Tcs.ComparisonTriangleMatrix
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonTriangleKappa
import AFTD.Kb.Tcs.ComparisonTriangle

/-!
# comparison_pi_ord_mulVec_phi2

Topic: quantum   Node: 1ac5bb8449ed

Provenance: helper lemma. Step of arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, Lemma 1 (quadratic_comparison_evaluation_kernel_and_projector)

Pi_ord fixes the quadratic evaluation vector phi_2(x) of every strict order x: U_triangle^T phi_2(x) = 0 by the triangle relations, hence also v_triangle^T phi_2(x) = 0.
-/

theorem comparison_pi_ord_mulVec_phi2 (n : ℕ) (x : Equiv.Perm (Fin n)) :
    Matrix.mulVec (comparison_pi_ord n) (comparison_phi2 x) = comparison_phi2 x := by
  classical
  have hU : Matrix.vecMul (comparison_phi2 x) (comparison_triangle_matrix n) = 0 := by
    funext t
    have := congrFun (comparison_triangle_kappa_mem_eval_ker n t) x
    simpa [Matrix.vecMul, Matrix.mulVec, dotProduct, comparison_triangle_matrix,
      comparison_eval_matrix, mul_comm] using this
  have hv : dotProduct (Matrix.mulVec (comparison_triangle_matrix n) (fun _ => 1))
      (comparison_phi2 x) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, hU, zero_dotProduct]
  have hUt : Matrix.mulVec (comparison_triangle_matrix n).transpose (comparison_phi2 x) = 0 := by
    rw [Matrix.mulVec_transpose, hU]
  unfold comparison_pi_ord
  simp only []
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hUt, Matrix.mulVec_zero, Matrix.vecMulVec_mulVec,
    hv]
  simp
