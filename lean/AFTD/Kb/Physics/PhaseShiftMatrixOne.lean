import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# phaseShiftMatrix_one

Topic: quantum_field_theory   Node: 643ceab462a5

Provenance: formalization of a published result. Source: Physlib, `phaseShiftMatrix_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The phase shift matrix for zero-phases is the identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The phase shift matrix for zero-phases is the identity. -/
lemma phaseShiftMatrix_one : phaseShiftMatrix 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseShiftMatrix, one_apply]
