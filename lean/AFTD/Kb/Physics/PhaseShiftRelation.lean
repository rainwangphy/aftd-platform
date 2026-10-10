import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix

/-!
# PhaseShiftRelation

Topic: quantum_field_theory   Node: 4e90662743bc

Provenance: formalization of a published result. Source: Physlib, `PhaseShiftRelation`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation on unitary matrices (CKM matrices) satisfied if two unitary matrices are related by phase shifts of quarks.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation on unitary matrices (CKM matrices) satisfied if two unitary matrices are related by phase shifts of quarks. -/
noncomputable def PhaseShiftRelation (U V : unitaryGroup (Fin 3) ℂ) : Prop :=
  ∃ a b c e f g, U = phaseShift a b c * V * phaseShift e f g
