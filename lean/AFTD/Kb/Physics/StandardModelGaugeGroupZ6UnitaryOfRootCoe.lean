import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRoot

/-!
# StandardModel.gaugeGroupℤ₆UnitaryOfRoot_coe

Topic: quantum_field_theory   Node: cc1426c12798

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆UnitaryOfRoot_coe`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.gaugeGroupℤ₆UnitaryOfRoot_coe
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
@[simp]
lemma StandardModel.gaugeGroupℤ₆UnitaryOfRoot_coe (α : rootsOfUnity 6 ℂ) :
    (gaugeGroupℤ₆UnitaryOfRoot α : ℂ) = ((α : ℂˣ) : ℂ) := rfl
