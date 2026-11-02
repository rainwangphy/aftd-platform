import AFTD.Prelude
import AFTD.Kb.Physics.IsingInverseSquareBulkFieldPolynomial
import AFTD.Kb.Physics.IsingInverseSquareOrderTwoFormulaLimit
import AFTD.Kb.Physics.IsingInverseSquareRingCoefficient

/-!
# ising_inverse_square_bulk_two_of_finite_formula

Topic: statistical_mechanics   Node: fed659cac9c5

Provenance: helper lemma. Helper for the second-order coefficient from arXiv:2610.39815, equations (3.15)–(3.16), and OP-806.

If the displayed second-order formula holds for every ring size L at least 2 and every real field, then the polynomial (1-y)(1+9y)/180 represents the bulk second-order field coefficient.
-/

theorem ising_inverse_square_bulk_two_of_finite_formula
    (hfinite : ∀ (L : ℕ), 2 ≤ L → ∀ h : ℝ,
      ising_inverse_square_ring_coefficient 2 L h =
      let u : ℝ := (L : ℝ)⁻¹
      let a := (1-u^2)/3
      let b := (1+10*u^2-11*u^4)/45
      let y := (Real.tanh h)^2
      (1-y^2)/4*b + y*(1-y)/2*(a^2-b)) :
    ising_inverse_square_bulk_field_polynomial 2
      (Polynomial.C (1 / 180 : ℝ) * (1 - Polynomial.X) * (1 + 9 * Polynomial.X)) := by
  intro h
  have hl := ising_inverse_square_order_two_formula_limit ((Real.tanh h)^2)
  have heq : (fun L : ℕ => ising_inverse_square_ring_coefficient 2 L h) =ᶠ[Filter.atTop]
      (fun L : ℕ =>
      let u : ℝ := (L : ℝ)⁻¹
      let a := (1-u^2)/3
      let b := (1+10*u^2-11*u^4)/45
      let y := (Real.tanh h)^2
      (1-y^2)/4*b + y*(1-y)/2*(a^2-b)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with L hL
    exact hfinite L hL h
  have heval : (Polynomial.C (1 / 180 : ℝ) * (1 - Polynomial.X) * (1 + 9 * Polynomial.X)).eval ((Real.tanh h)^2) =
      (1-(Real.tanh h)^2)*(1+9*(Real.tanh h)^2)/180 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  rw [heval]
  exact hl.congr' heq.symm
