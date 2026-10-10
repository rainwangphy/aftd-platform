import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoInvApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceAbsMulGaussianIntegrable

/-!
# Lorentz.SL2C.rotationZToAxis_one_mul_diagonal_mul_inv

Topic: special_relativity   Node: fa12663301d2

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.rotationZToAxis_one_mul_diagonal_mul_inv`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/AxisRotations.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugating `diag(a, b)` by the rotation to the `y`-axis expresses it in the `y`-axis basis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- Conjugating `diag(a, b)` by the rotation to the `y`-axis expresses it in the `y`-axis basis. -/
lemma Lorentz.SL2C.rotationZToAxis_one_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 1).1 * !![a, 0; 0, b] * ((rotationZToAxis 1)⁻¹).1 =
      !![(a + b) / 2, -Complex.I * (a - b) / 2;
        Complex.I * (a - b) / 2, (a + b) / 2] := by
  have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by simp
  ext j k
  fin_cases j <;> fin_cases k
  all_goals
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_one_apply,
      rotationZToAxis_one_inv_apply]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.smul_apply, of_apply, cons_val',
      cons_val_zero, cons_val_fin_one, smul_eq_mul, mul_one, cons_val_one, mul_zero,
      add_zero, zero_add, mul_neg, neg_mul, Fin.mk_one]
    field_simp
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  all_goals ring
