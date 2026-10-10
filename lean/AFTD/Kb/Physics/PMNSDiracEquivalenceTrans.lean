import AFTD.Prelude
import AFTD.Kb.Physics.PMNSDiracEquivalence
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseMul
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseShiftCoeMatrix
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolution

/-!
# PMNSDiracEquivalence_trans

Topic: quantum_field_theory   Node: 8e18a3fa0fdf

Provenance: formalization of a published result. Source: Physlib, `PMNSDiracEquivalence_trans`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `PMNSDiracEquivalence` is transitive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation `PMNSDiracEquivalence` is transitive. -/
lemma PMNSDiracEquivalence_trans {U V W : unitaryGroup (Fin 3) ℂ} :
    PMNSDiracEquivalence U V → PMNSDiracEquivalence V W → PMNSDiracEquivalence U W := by
    rintro ⟨θ1, φ1, hUV⟩ ⟨θ2, φ2, hVW⟩
    refine ⟨θ1 + θ2, φ1 + φ2, ?_⟩
    simp only [hUV, hVW, ← mul_assoc, diagPhase_mul]
    simp [mul_assoc, diagPhase_mul, add_comm]
