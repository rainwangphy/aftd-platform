import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar

/-!
# diagPhase_mul

Topic: quantum_field_theory   Node: 0ade6dcf3013

Provenance: formalization of a published result. Source: Physlib, `diagPhase_mul`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

lemma stating that multiplying two phase matrices is equivalent to adding the phases
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- lemma stating that multiplying two phase matrices is equivalent to adding the phases -/
@[simp]
lemma diagPhase_mul (θ φ : Fin 3 → ℝ) :
    diagPhase θ * diagPhase φ = diagPhase (θ + φ) := by
    show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
    simp [Matrix.diagonal_mul_diagonal, ← exp_add, mul_add]
