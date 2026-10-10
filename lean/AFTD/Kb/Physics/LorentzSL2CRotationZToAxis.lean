import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceAbsMulGaussianIntegrable
import AFTD.Kb.Tcs.NAEtoColorClauseNodeColor

/-!
# Lorentz.SL2C.rotationZToAxis

Topic: special_relativity   Node: 145386250da1

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.rotationZToAxis`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/AxisRotations.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `SL(2,ℂ)` rotation carrying the `z`-axis to axis `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The `SL(2,ℂ)` rotation carrying the `z`-axis to axis `i`. -/
noncomputable def Lorentz.SL2C.rotationZToAxis : Fin 3 → SL(2,ℂ)
  | 0 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow]
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt]⟩
  | 1 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow,
          Complex.I_mul_I]
        norm_num [← Complex.ofReal_pow, Real.sq_sqrt]⟩
  | 2 => 1
