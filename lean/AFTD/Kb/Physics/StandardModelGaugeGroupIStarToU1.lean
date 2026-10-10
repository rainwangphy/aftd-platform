import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupIToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU2

/-!
# StandardModel.GaugeGroupI.star_toU1

Topic: quantum_field_theory   Node: 93b4b5e2c221

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.star_toU1`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.GaugeGroupI.star_toU1
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
@[simp]
lemma StandardModel.GaugeGroupI.star_toU1 (g : GaugeGroupI) : toU1 (star g) = star (toU1 g) := rfl
