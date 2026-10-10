import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupIExt
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU3OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU2OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupIToU1
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
# StandardModel.gaugeGroupℤ₆Hom

Topic: quantum_field_theory   Node: 0e724f44c482

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆Hom`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The homomorphism from sixth roots of unity to `GaugeGroupI`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The homomorphism from sixth roots of unity to `GaugeGroupI`. -/
noncomputable def StandardModel.gaugeGroupℤ₆Hom : rootsOfUnity 6 ℂ →* GaugeGroupI where
  toFun := gaugeGroupℤ₆OfRoot
  map_one' := by
    apply GaugeGroupI.ext
    · change gaugeGroupℤ₆SU3OfRoot 1 = 1
      ext i j
      simp [gaugeGroupℤ₆SU3OfRoot, Matrix.scalar_apply]
    · change gaugeGroupℤ₆SU2OfRoot 1 = 1
      ext i j
      simp [gaugeGroupℤ₆SU2OfRoot, gaugeGroupℤ₆UnitaryOfRoot, Matrix.scalar_apply]
    · change gaugeGroupℤ₆UnitaryOfRoot 1 = 1
      ext
      simp [gaugeGroupℤ₆UnitaryOfRoot]
  map_mul' α β := by
    apply GaugeGroupI.ext
    · change gaugeGroupℤ₆SU3OfRoot (α * β) =
        gaugeGroupℤ₆SU3OfRoot α * gaugeGroupℤ₆SU3OfRoot β
      ext i j
      simp [gaugeGroupℤ₆SU3OfRoot, Matrix.scalar_apply, pow_two, mul_left_comm, mul_comm]
    · change gaugeGroupℤ₆SU2OfRoot (α * β) =
        gaugeGroupℤ₆SU2OfRoot α * gaugeGroupℤ₆SU2OfRoot β
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gaugeGroupℤ₆SU2OfRoot, gaugeGroupℤ₆UnitaryOfRoot, Matrix.scalar_apply,
          pow_succ] <;>
        ring
    · change gaugeGroupℤ₆UnitaryOfRoot (α * β) =
        gaugeGroupℤ₆UnitaryOfRoot α * gaugeGroupℤ₆UnitaryOfRoot β
      ext
      simp [gaugeGroupℤ₆UnitaryOfRoot]
