import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix
import AFTD.Kb.Physics.PhaseShiftRelation
import AFTD.Kb.Physics.PhaseShiftRelationEquiv
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# CKMMatrixSetoid

Topic: quantum_field_theory   Node: 344cbf3b2095

Provenance: formalization of a published result. Source: Physlib, `CKMMatrixSetoid`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The setoid of CKM matrices defined by phase shifts of fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The setoid of CKM matrices defined by phase shifts of fermions. -/
noncomputable instance CKMMatrixSetoid : Setoid CKMMatrix := ⟨PhaseShiftRelation, phaseShiftRelation_equiv⟩
