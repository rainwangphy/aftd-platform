import AFTD.Prelude

/-!
# LinearMap.map_smul_of_commutesI

Topic: classical_mechanics   Node: 028e78dd610d

Provenance: formalization of a published result. Source: Physlib, `LinearMap.map_smul_of_commutesI`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/ComplexLinear.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `ℝ`-linear map commuting with `i` along `v` commutes with every complex scalar along `v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E] in
/-- An `ℝ`-linear map commuting with `i` along `v` commutes with every complex scalar along `v`. -/
lemma LinearMap.map_smul_of_commutesI (L : V →ₗ[ℝ] E) {v : V}
    (h : L (Complex.I • v) = Complex.I • L v) (c : ℂ) :
    L (c • v) = c • L v := by
  have hV : c • v = c.re • v + c.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    simp only [add_smul, mul_smul, ← Complex.coe_algebraMap, algebraMap_smul]
  have hE : c • L v = c.re • L v + c.im • (Complex.I • L v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    simp only [add_smul, mul_smul, ← Complex.coe_algebraMap, algebraMap_smul]
  rw [hV, map_add, L.map_smul, L.map_smul, h, hE]
