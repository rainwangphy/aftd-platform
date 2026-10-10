import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.LeptonPhaseShift
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseMul
import AFTD.Kb.Physics.DiagPhaseShiftCoeMatrix

/-!
# neutrinoPhaseShift

Topic: quantum_field_theory   Node: 080a1d0dac72

Provenance: formalization of a published result. Source: Physlib, `neutrinoPhaseShift`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The neutrino phase shift matrix as a `3×3` complex matrix, given three reals `d e f`. This dictates the phase shift freedom of the neutrino sector (If neutrinos are Dirac).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The neutrino phase shift matrix as a `3×3` complex matrix, given three reals `d e f`. This dictates the phase shift freedom of the neutrino sector (If neutrinos are Dirac). -/
noncomputable def neutrinoPhaseShift (d e f : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then d else if i = 1 then e else f)
