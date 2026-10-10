import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftMatrix
import AFTD.Kb.Physics.PhaseShiftMatrixStar
import AFTD.Kb.Physics.PhaseShiftMatrixMul
import AFTD.Kb.Physics.PhaseShiftMatrixOne

/-!
# phaseShift

Topic: quantum_field_theory   Node: cc87da85a467

Provenance: formalization of a published result. Source: Physlib, `phaseShift`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given three real numbers `a b c` the unitary matrix with `exp (I * a)` etc on the leading diagonal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
set_option backward.isDefEq.respectTransparency false in
/-- Given three real numbers `a b c` the unitary matrix with `exp (I * a)` etc on the leading diagonal. -/
@[simps!]
noncomputable def phaseShift (a b c : ℝ) : unitaryGroup (Fin 3) ℂ :=
  ⟨phaseShiftMatrix a b c,
  by
    rw [mem_unitaryGroup_iff]
    change _ * (phaseShiftMatrix a b c)ᴴ = 1
    rw [phaseShiftMatrix_star, phaseShiftMatrix_mul, ← phaseShiftMatrix_one]
    simp only [phaseShiftMatrix, add_neg_cancel, ofReal_zero, mul_zero, exp_zero]⟩
