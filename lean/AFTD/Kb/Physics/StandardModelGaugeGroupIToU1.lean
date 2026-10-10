import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI

/-!
# StandardModel.GaugeGroupI.toU1

Topic: quantum_field_theory   Node: 06e8592a8856

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.toU1`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying element of `U(1)` of an element in `GaugeGroupI`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The underlying element of `U(1)` of an element in `GaugeGroupI`. -/
def StandardModel.GaugeGroupI.toU1 : GaugeGroupI →* unitary ℂ where
  toFun g := g.2.2
  map_one' := rfl
  map_mul' _ _ := rfl
