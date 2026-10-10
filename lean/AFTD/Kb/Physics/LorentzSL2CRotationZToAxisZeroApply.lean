import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CRotationZToAxis

/-!
# Lorentz.SL2C.rotationZToAxis_zero_apply

Topic: special_relativity   Node: 564695724a03

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.rotationZToAxis_zero_apply`. Lean proof by Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/AxisRotations.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The matrix entries of the rotation carrying the `z`-axis to the `x`-axis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix MatrixGroups in
/-- The matrix entries of the rotation carrying the `z`-axis to the `x`-axis. -/
@[simp] lemma Lorentz.SL2C.rotationZToAxis_zero_apply (j k : Fin 2) :
    (rotationZToAxis 0).1 j k =
      ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1]) j k := rfl
