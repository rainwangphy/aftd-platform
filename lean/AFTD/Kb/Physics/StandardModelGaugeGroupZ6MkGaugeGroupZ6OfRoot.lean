import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelInstGroupGaugeGroupZ6
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6Mk
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SubGroup
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SubGroupNormal
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRootMem
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
# StandardModel.GaugeGroupℤ₆.mk_gaugeGroupℤ₆OfRoot

Topic: quantum_field_theory   Node: 8832b6b81814

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupℤ₆.mk_gaugeGroupℤ₆OfRoot`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.GaugeGroupℤ₆.mk_gaugeGroupℤ₆OfRoot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
@[simp]
lemma StandardModel.GaugeGroupℤ₆.mk_gaugeGroupℤ₆OfRoot (α : rootsOfUnity 6 ℂ) :
    mk (gaugeGroupℤ₆OfRoot α) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (gaugeGroupℤ₆OfRoot_mem α)
