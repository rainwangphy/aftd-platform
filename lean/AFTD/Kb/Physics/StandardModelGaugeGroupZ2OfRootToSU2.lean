import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU2OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ2RootToZ6Root
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
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstInvolutiveStar

/-!
# StandardModel.gaugeGroupℤ₂OfRoot_toSU2

Topic: quantum_field_theory   Node: 33953788e0cc

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₂OfRoot_toSU2`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.gaugeGroupℤ₂OfRoot_toSU2
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
@[simp]
lemma StandardModel.gaugeGroupℤ₂OfRoot_toSU2 (α : rootsOfUnity 2 ℂ) :
    GaugeGroupI.toSU2 (gaugeGroupℤ₂OfRoot α) =
      gaugeGroupℤ₆SU2OfRoot (gaugeGroupℤ₂RootToℤ₆Root α) := rfl
