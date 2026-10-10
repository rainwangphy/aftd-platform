import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix
import AFTD.Kb.Physics.CKMMatrixSetoid
import AFTD.Kb.Physics.VAbs
import AFTD.Kb.Physics.VAbs'

/-!
# VudAbs

Topic: quantum_field_theory   Node: cb8a6511a801

Provenance: formalization of a published result. Source: Physlib, `VudAbs`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The absolute value of the `ud`th element of a representative of an equivalence class of CKM matrices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The absolute value of the `ud`th element of a representative of an equivalence class of CKM matrices. -/
@[simp]
noncomputable abbrev VudAbs := VAbs 0 0
