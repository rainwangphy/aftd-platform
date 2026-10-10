import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ3SubGroup
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
# StandardModel.GaugeGroupℤ₃

Topic: quantum_field_theory   Node: 194148bcb8e6

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupℤ₃`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gauge group of the Standard Model with a ℤ₃-quotient, i.e., the quotient of `GaugeGroupI` by the ℤ₃-subgroup `gaugeGroupℤ₃SubGroup`. See https://math.ucr.edu/home/baez/guts.pdf [ref: baez_guts_notes]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The gauge group of the Standard Model with a ℤ₃-quotient, i.e., the quotient of `GaugeGroupI` by the ℤ₃-subgroup `gaugeGroupℤ₃SubGroup`. See https://math.ucr.edu/home/baez/guts.pdf [ref: baez_guts_notes] -/
def StandardModel.GaugeGroupℤ₃ : Type :=
  GaugeGroupI ⧸ gaugeGroupℤ₃SubGroup
