import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupIExt
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU3OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU2OfRoot
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
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstInvolutiveStar

/-!
# StandardModel.gaugeGroupℤ₆OfRoot_mem_center

Topic: quantum_field_theory   Node: 136d6980e3b9

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆OfRoot_mem_center`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.gaugeGroupℤ₆OfRoot_mem_center
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
lemma StandardModel.gaugeGroupℤ₆OfRoot_mem_center (α : rootsOfUnity 6 ℂ) :
    gaugeGroupℤ₆OfRoot α ∈ Subgroup.center GaugeGroupI := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine GaugeGroupI.ext ?_ ?_ (mul_comm _ _) <;> ext i j <;>
    simp [map_mul, gaugeGroupℤ₆SU3OfRoot, gaugeGroupℤ₆SU2OfRoot, Matrix.scalar_apply, mul_comm]
