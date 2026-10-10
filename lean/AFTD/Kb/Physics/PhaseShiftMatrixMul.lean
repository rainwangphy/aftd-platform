import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# phaseShiftMatrix_mul

Topic: quantum_field_theory   Node: a50c608c22a7

Provenance: formalization of a published result. Source: Physlib, `phaseShiftMatrix_mul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The multiple of two phase shift matrices is equal to the phase shift matrix with added phases.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
set_option backward.isDefEq.respectTransparency false in
/-- The multiple of two phase shift matrices is equal to the phase shift matrix with added phases. -/
lemma phaseShiftMatrix_mul (a b c d e f : ℝ) :
    phaseShiftMatrix a b c * phaseShiftMatrix d e f = phaseShiftMatrix (a + d) (b + e) (c + f) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseShiftMatrix, mul_apply, Fin.sum_univ_three, ← exp_add, mul_add]
