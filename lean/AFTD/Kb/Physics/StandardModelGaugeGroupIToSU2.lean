import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI

/-!
# StandardModel.GaugeGroupI.toSU2

Topic: quantum_field_theory   Node: d56c250e8d97

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.toSU2`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying element of `SU(2)` of an element in `GaugeGroupI`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The underlying element of `SU(2)` of an element in `GaugeGroupI`. -/
def StandardModel.GaugeGroupI.toSU2 : GaugeGroupI →* specialUnitaryGroup (Fin 2) ℂ where
  toFun g := g.2.1
  map_one' := rfl
  map_mul' _ _ := rfl
