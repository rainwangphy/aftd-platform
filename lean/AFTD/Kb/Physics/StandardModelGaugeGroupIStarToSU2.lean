import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU3

/-!
# StandardModel.GaugeGroupI.star_toSU2

Topic: quantum_field_theory   Node: 653f8ed65470

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.star_toSU2`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.GaugeGroupI.star_toSU2
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
@[simp]
lemma StandardModel.GaugeGroupI.star_toSU2 (g : GaugeGroupI) : toSU2 (star g) = star (toSU2 g) := rfl
