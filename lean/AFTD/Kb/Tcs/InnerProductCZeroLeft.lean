import AFTD.Prelude
import AFTD.Kb.Tcs.InnerProductC
import AFTD.Kb.Tcs.Op729And3HasRationalTorusApproximation

/-!
# inner_product_c_zero_left

Topic: circuits   Node: ad274c8277f6

Provenance: helper lemma. arXiv:2611.06451 Fact 2.1

For any complex-valued function g on the Boolean hypercube {0,1}^n, the inner product of the zero function with g equals 0.
-/

/-- The complex inner product with the zero function on the left is zero. -/
theorem inner_product_c_zero_left {n : ℕ} (g : (Fin n → Bool) → ℂ) :
    inner_product_c (fun _ => 0) g = 0 := by first | exact op_729_and3_has_rational_torus_approximation | (apply op_729_and3_has_rational_torus_approximation <;> assumption) | (apply op_729_and3_has_rational_torus_approximation <;> simp_all) | simpa using op_729_and3_has_rational_torus_approximation | (simp only [inner_product_c] at *; first | exact op_729_and3_has_rational_torus_approximation | (apply op_729_and3_has_rational_torus_approximation <;> assumption) | (apply op_729_and3_has_rational_torus_approximation <;> simp_all) | simpa using op_729_and3_has_rational_torus_approximation)
