import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpToSolNSQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpToSolNSQuadCube
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp

/-!
# MSSMACC.AnomalyFreePerp.toSolNS

Topic: quantum_field_theory   Node: 6b20e9ad80fc

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.toSolNS`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given an `R` perpendicular to `Y₃` and `B₃`, an element of `Sols`. This map is not surjective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- Given an `R` perpendicular to `Y₃` and `B₃`, an element of `Sols`. This map is not surjective. -/
def MSSMACC.AnomalyFreePerp.toSolNS : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, a, _, _) =>
  a • AnomalyFreeMk'' (toSolNSQuad R) (toSolNSQuad_cube R)
