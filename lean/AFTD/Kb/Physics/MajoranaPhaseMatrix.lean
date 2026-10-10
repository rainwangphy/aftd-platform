import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.LeptonPhaseShift
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseMul
import AFTD.Kb.Physics.DiagPhaseShiftCoeMatrix

/-!
# majoranaPhaseMatrix

Topic: quantum_field_theory   Node: 2ad6e5648285

Provenance: formalization of a published result. Source: Physlib, `majoranaPhaseMatrix`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If neutrinos are Majorana particles, then the neutrino phase shift matrix is physical, and cannot be absorbed into the definition of the neutrino fields.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- If neutrinos are Majorana particles, then the neutrino phase shift matrix is physical, and cannot be absorbed into the definition of the neutrino fields. -/
noncomputable def majoranaPhaseMatrix (α1 α2 : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then 0 else if i = 1 then α1/2 else α2/2)
