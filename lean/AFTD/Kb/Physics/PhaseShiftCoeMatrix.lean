import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# phaseShift_coe_matrix

Topic: quantum_field_theory   Node: 3aa4b8170c91

Provenance: formalization of a published result. Source: Physlib, `phaseShift_coe_matrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying matrix of the phase-shift element of the unitary group is the phase-shift matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The underlying matrix of the phase-shift element of the unitary group is the phase-shift matrix. -/
lemma phaseShift_coe_matrix (a b c : ℝ) : ↑(phaseShift a b c) = phaseShiftMatrix a b c := rfl
