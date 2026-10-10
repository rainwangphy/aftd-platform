import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseMul
import AFTD.Kb.Physics.DiagPhaseShiftCoeMatrix

/-!
# PMNSDiracEquivalence

Topic: quantum_field_theory   Node: 505f77ff0df3

Provenance: formalization of a published result. Source: Physlib, `PMNSDiracEquivalence`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Dirac PMNS matrix equivalence relations
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The Dirac PMNS matrix equivalence relations -/
noncomputable def PMNSDiracEquivalence (U V : unitaryGroup (Fin 3) ℂ) : Prop :=
  ∃ (θ φ : Fin 3 → ℝ),
  U = diagPhase θ * V * diagPhase φ
