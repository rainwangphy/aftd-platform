import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoApply

/-!
# Lorentz.SL2C.rotationZToAxis_zero_inv_apply

Topic: special_relativity   Node: acfca7f7406c

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.rotationZToAxis_zero_inv_apply`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/AxisRotations.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The matrix entries of the inverse rotation from the `x`-axis to the `z`-axis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The matrix entries of the inverse rotation from the `x`-axis to the `z`-axis. -/
@[simp] lemma Lorentz.SL2C.rotationZToAxis_zero_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 0)⁻¹).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, 1; -1, 1]) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]
