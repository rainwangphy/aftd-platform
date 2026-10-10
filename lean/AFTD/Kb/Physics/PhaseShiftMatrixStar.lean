import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# phaseShiftMatrix_star

Topic: quantum_field_theory   Node: d887214dea83

Provenance: formalization of a published result. Source: Physlib, `phaseShiftMatrix_star`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conjugate transpose of the phase shift matrix is the phase-shift matrix with negated phases.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
set_option backward.isDefEq.respectTransparency false in
/-- The conjugate transpose of the phase shift matrix is the phase-shift matrix with negated phases. -/
lemma phaseShiftMatrix_star (a b c : ℝ) :
    (phaseShiftMatrix a b c)ᴴ = phaseShiftMatrix (- a) (- b) (- c) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseShiftMatrix, conjTranspose_apply, ← exp_conj, conj_I, conj_ofReal]
