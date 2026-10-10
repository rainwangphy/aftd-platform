import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix
import AFTD.Kb.Physics.CKMMatrixSetoid
import AFTD.Kb.Physics.PhaseShiftApply
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# phaseShiftApply.equiv

Topic: quantum_field_theory   Node: ecb209edccdc

Provenance: formalization of a published result. Source: Physlib, `phaseShiftApply.equiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A CKM matrix is equivalent to a phase-shift of itself.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- A CKM matrix is equivalent to a phase-shift of itself. -/
lemma phaseShiftApply.equiv (V : CKMMatrix) (a b c d e f : ℝ) :
    V ≈ phaseShiftApply V a b c d e f := by
  symm
  exact ⟨a, b, c, d, e, f, rfl⟩
