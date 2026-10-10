import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6
import AFTD.Kb.Physics.StandardModelInstGroupGaugeGroupZ6
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SubGroup
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SubGroupNormal
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1SubgroupToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1SubgroupToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1SubgroupToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRootCoe
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRootToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRootToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRootToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6HomApply
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6HomToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6HomToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6HomToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstInvolutiveStar

/-!
# StandardModel.GaugeGroupℤ₆.mk

Topic: quantum_field_theory   Node: be5f055722cd

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupℤ₆.mk`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quotient map from `GaugeGroupI` to `GaugeGroupℤ₆`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The quotient map from `GaugeGroupI` to `GaugeGroupℤ₆`. -/
noncomputable def StandardModel.GaugeGroupℤ₆.mk : GaugeGroupI →* GaugeGroupℤ₆ :=
  QuotientGroup.mk' gaugeGroupℤ₆SubGroup
