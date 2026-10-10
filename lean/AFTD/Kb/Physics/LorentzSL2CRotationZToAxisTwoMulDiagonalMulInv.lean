import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisTwoApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisZeroInvApply
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxisOneInvApply

/-!
# Lorentz.SL2C.rotationZToAxis_two_mul_diagonal_mul_inv

Topic: special_relativity   Node: b7458c847e11

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.rotationZToAxis_two_mul_diagonal_mul_inv`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/AxisRotations.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugating `diag(a, b)` by the identity rotation leaves it unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- Conjugating `diag(a, b)` by the identity rotation leaves it unchanged. -/
lemma Lorentz.SL2C.rotationZToAxis_two_mul_diagonal_mul_inv (a b : ℂ) :
    (rotationZToAxis 2).1 * !![a, 0; 0, b] * ((rotationZToAxis 2)⁻¹).1 =
      !![a, 0; 0, b] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_two_apply,
      rotationZToAxis_two_inv_apply] <;>
    simp [Matrix.one_apply]
