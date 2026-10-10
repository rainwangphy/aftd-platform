import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SubGroup
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6Hom
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
# StandardModel.mem_gaugeGroupℤ₆SubGroup_iff

Topic: quantum_field_theory   Node: f7b7da575d13

Provenance: formalization of a published result. Source: Physlib, `StandardModel.mem_gaugeGroupℤ₆SubGroup_iff`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.mem_gaugeGroupℤ₆SubGroup_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
lemma StandardModel.mem_gaugeGroupℤ₆SubGroup_iff (g : GaugeGroupI) :
    g ∈ gaugeGroupℤ₆SubGroup ↔ ∃ α : rootsOfUnity 6 ℂ, gaugeGroupℤ₆OfRoot α = g := by
  simp [gaugeGroupℤ₆SubGroup]
