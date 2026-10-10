import AFTD.Prelude
import AFTD.Kb.Physics.PMNSDiracEquivalence
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseMul
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseShiftCoeMatrix
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolution

/-!
# PMNSDiracEquivalence_symm

Topic: quantum_field_theory   Node: 365e02cbc26c

Provenance: formalization of a published result. Source: Physlib, `PMNSDiracEquivalence_symm`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `PMNSDiracEquivalence` is symmetric.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation `PMNSDiracEquivalence` is symmetric. -/
lemma PMNSDiracEquivalence_symm :
    ∀ U V : unitaryGroup (Fin 3) ℂ, PMNSDiracEquivalence U V → PMNSDiracEquivalence V U := by
    rintro U V ⟨θ, φ, h'⟩
    refine ⟨-θ, -φ, ?_⟩
    simp only [h', ← mul_assoc, diagPhase_mul]
    simp [mul_assoc, diagPhase_mul, add_neg_cancel, neg_add_cancel]
