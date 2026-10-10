import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU3OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU2OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1SubgroupToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1SubgroupToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIOfU1SubgroupToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRootCoe
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstInvolutiveStar

/-!
# StandardModel.gaugeGroupℤ₆OfRoot

Topic: quantum_field_theory   Node: a8f2bc56880a

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆OfRoot`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The element of `GaugeGroupI` associated to a sixth root of unity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The element of `GaugeGroupI` associated to a sixth root of unity. -/
noncomputable def StandardModel.gaugeGroupℤ₆OfRoot (α : rootsOfUnity 6 ℂ) : GaugeGroupI :=
  (gaugeGroupℤ₆SU3OfRoot α, gaugeGroupℤ₆SU2OfRoot α, gaugeGroupℤ₆UnitaryOfRoot α)
