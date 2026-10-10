import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction

/-!
# ACCSystem

Topic: quantum_field_theory   Node: 5e0d01f02762

Provenance: formalization of a published result. Source: Physlib, `ACCSystem`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of charges plus the anomaly cancellation conditions. In many physical settings these conditions are derived formally from the gauge group and the fermionic representations. They arise from triangle Feynman diagrams, and can also be obtained using index-theoretic or characteristic-class constructions. In this file, we take the resulting conditions as input data: linear, quadratic and cubic homogeneous forms on the space of rational charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type of charges plus the anomaly cancellation conditions. In many physical settings these conditions are derived formally from the gauge group and the fermionic representations. They arise from triangle Feynman diagrams, and can also be obtained using index-theoretic or characteristic-class constructions. In this file, we take the resulting conditions as input data: linear, quadratic and cubic homogeneous forms on the space of rational charges. -/
structure ACCSystem extends ACCSystemQuad where
  /-- The cubic ACC. -/
  cubicACC : HomogeneousCubic toACCSystemCharges.Charges
