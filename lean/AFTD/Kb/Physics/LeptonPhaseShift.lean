import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseMul
import AFTD.Kb.Physics.DiagPhaseShiftCoeMatrix

/-!
# leptonPhaseShift

Topic: quantum_field_theory   Node: 3ea118471c03

Provenance: formalization of a published result. Source: Physlib, `leptonPhaseShift`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Lepton phase shift matrix as a `3×3` complex matrix, given three reals `a b c`. This dictates the phase shift freedom of the charged lepton sector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The Lepton phase shift matrix as a `3×3` complex matrix, given three reals `a b c`. This dictates the phase shift freedom of the charged lepton sector. -/
noncomputable def leptonPhaseShift (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagPhase (fun i => if i = 0 then a else if i = 1 then b else c)
