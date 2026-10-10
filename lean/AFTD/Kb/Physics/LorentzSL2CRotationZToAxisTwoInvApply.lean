import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneInvApply

/-!
# Lorentz.SL2C.rotationZToAxis_two_inv_apply

Topic: special_relativity   Node: a2b2da0f14b6

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.rotationZToAxis_two_inv_apply`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/AxisRotations.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inverse rotation from the `z`-axis to itself is the identity matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The inverse rotation from the `z`-axis to itself is the identity matrix. -/
@[simp] lemma Lorentz.SL2C.rotationZToAxis_two_inv_apply (j k : Fin 2) :
    ((rotationZToAxis 2)⁻¹).1 j k = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]
