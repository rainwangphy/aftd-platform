import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix
import AFTD.Kb.Physics.PhaseShiftApply
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix
import AFTD.Kb.Physics.PhaseShiftCoeMatrix
import AFTD.Kb.Physics.CKMMatrixSetoid

/-!
# phaseShiftApply.cb

Topic: quantum_field_theory   Node: 98a1f2fdc5c8

Provenance: formalization of a published result. Source: Physlib, `phaseShiftApply.cb`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `cb` component of the CKM matrix obtained after applying a phase shift.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
set_option backward.isDefEq.respectTransparency false in
/-- The `cb` component of the CKM matrix obtained after applying a phase shift. -/
lemma phaseShiftApply.cb (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 2 = cexp (b * I + f * I) * V.1 1 2 := by
  simp only [Fin.isValue, phaseShiftApply_coe, Submonoid.coe_mul, phaseShift_coe_matrix,
    phaseShiftMatrix, mul_apply, cons_val', cons_val_fin_one, cons_val_one, cons_val_zero,
    Fin.sum_univ_three, zero_mul, zero_add, cons_val, add_zero, mul_zero, exp_add]
  ring_nf
