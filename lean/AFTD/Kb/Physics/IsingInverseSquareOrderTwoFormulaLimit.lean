import AFTD.Prelude

/-!
# ising_inverse_square_order_two_formula_limit

Topic: statistical_mechanics   Node: 492db0d41bf1

Provenance: helper lemma. Helper for the second-order coefficient from arXiv:2610.39815, equations (3.15)–(3.16), and OP-806.

For every real y, the finite-ring rational expression from the second-order coefficient formula tends to (1-y)(1+9y)/180 as the natural ring size tends to infinity.
-/

theorem ising_inverse_square_order_two_formula_limit (y : ℝ) :
  Filter.Tendsto (fun L : ℕ =>
    let u : ℝ := (L : ℝ)⁻¹
    let a := (1-u^2)/3
    let b := (1+10*u^2-11*u^4)/45
    (1-y^2)/4*b + y*(1-y)/2*(a^2-b))
    Filter.atTop (nhds ((1-y)*(1+9*y)/180)) := by
  have hu : Filter.Tendsto (fun L : ℕ => (L : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Continuous (fun u : ℝ =>
    let a := (1-u^2)/3
    let b := (1+10*u^2-11*u^4)/45
    (1-y^2)/4*b + y*(1-y)/2*(a^2-b)) := by
    fun_prop
  have hh := (hc.tendsto 0).comp hu
  convert hh using 1 <;> first | rfl | (congr 1; norm_num; ring)
