import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixOrderFourRowSumZeroMulVecConst

/-!
# matrix_row_sum_zero_shifted_eigenvector

Topic: graphs   Node: e938afe67d70

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

For real order-four matrices with zero row sums, an eigenvector of one with nonzero eigenvalue can be adjusted by a constant to give an eigenvector of the other when its image differs from a nonzero scalar multiple by a constant.
-/

theorem matrix_row_sum_zero_shifted_eigenvector
    (L K : Matrix (Fin 4) (Fin 4) ℝ)
    (hrL : ∀ i, ∑ j, L i j = 0) (hrK : ∀ i, ∑ j, K i j = 0)
    (v : Fin 4 → ℂ) (hv0 : v ≠ 0) (z : ℂ) (hz : z ≠ 0)
    (hv : (L.map (algebraMap ℝ ℂ)).mulVec v = z • v)
    (lam c : ℂ) (hlam : lam ≠ 0)
    (hKv : (K.map (algebraMap ℝ ℂ)).mulVec v = fun i => lam * v i + c) :
    ∃ w : Fin 4 → ℂ, w ≠ 0 ∧
      (K.map (algebraMap ℝ ℂ)).mulVec w = lam • w := by
  let w : Fin 4 → ℂ := v + fun _ => c / lam
  have hw0 : w ≠ 0 := by
    intro hh
    have hvconst : v = fun _ => -(c / lam) := by
      ext i
      have hi := congrFun hh i
      change v i + c / lam = 0 at hi
      linear_combination hi
    have hzero : (L.map (algebraMap ℝ ℂ)).mulVec v = 0 := by
      rw [hvconst]
      exact matrix_order_four_row_sum_zero_mulVec_const L hrL _
    have hsm : z • v = 0 := hv.symm.trans hzero
    exact hv0 ((smul_eq_zero.mp hsm).resolve_left hz)
  refine ⟨w, hw0, ?_⟩
  change (K.map (algebraMap ℝ ℂ)).mulVec (v + fun _ => c / lam) = _
  rw [Matrix.mulVec_add, matrix_order_four_row_sum_zero_mulVec_const K hrK, add_zero, hKv]
  ext i
  change lam * v i + c = lam * (v i + c / lam)
  field_simp
  <;> ring
