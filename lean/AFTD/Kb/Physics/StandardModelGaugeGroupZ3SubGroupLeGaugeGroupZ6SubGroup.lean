import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3SubGroup
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SubGroup
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3Hom
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRootMem
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3RootToZ6Root
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
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6MkGaugeGroupZ6OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2OfRootToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2OfRootToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2OfRootToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2HomToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2HomToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2HomToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3OfRootToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3OfRootToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3OfRootToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3HomApply
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3HomToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3HomToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3HomToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstInvolutiveStar

/-!
# StandardModel.gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup

Topic: quantum_field_theory   Node: 1b448b1790cb

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
lemma StandardModel.gaugeGroupℤ₃SubGroup_le_gaugeGroupℤ₆SubGroup :
    gaugeGroupℤ₃SubGroup ≤ gaugeGroupℤ₆SubGroup := by
  rintro g ⟨α, rfl⟩
  exact gaugeGroupℤ₆OfRoot_mem (gaugeGroupℤ₃RootToℤ₆Root α)
