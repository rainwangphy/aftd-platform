import AFTD.Prelude

/-!
# SMRHN.PlusU1.ElevenPlane.quadCoeff

Topic: quantum_field_theory   Node: 3320aafc68c7

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.ElevenPlane.quadCoeff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/PlaneNonSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The coefficients of the quadratic equation in our basis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The coefficients of the quadratic equation in our basis. -/
@[simp]
def SMRHN.PlusU1.ElevenPlane.quadCoeff : Fin 11 → ℚ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0]
