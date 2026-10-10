import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhaseUnitary
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseMul

/-!
# diagPhaseShift_coe_matrix

Topic: quantum_field_theory   Node: 20ad5bf746d7

Provenance: formalization of a published result. Source: Physlib, `diagPhaseShift_coe_matrix`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying matrix of the phase-shift element of the unitary group is the phase-shift matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The underlying matrix of the phase-shift element of the unitary group is the phase-shift matrix. -/
@[simp]
lemma diagPhaseShift_coe_matrix (θ : Fin 3 → ℝ) : ↑(diagPhaseUnitary θ) = diagPhase θ := rfl
