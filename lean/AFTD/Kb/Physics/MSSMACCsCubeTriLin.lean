import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFun
import AFTD.Kb.Physics.TriLinearSymmMk3
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunMapSmul1
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunMapAdd1
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunSwap1
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunSwap2
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMACCs.cubeTriLin

Topic: quantum_field_theory   Node: 1aaec62f4b20

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.cubeTriLin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The symmetric trilinear form used to define the cubic ACC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
/-- The symmetric trilinear form used to define the cubic ACC. -/
@[simps!]
def MSSMACCs.cubeTriLin : TriLinearSymm MSSMCharges.Charges := TriLinearSymm.mk₃
  cubeTriLinToFun
  cubeTriLinToFun_map_smul₁
  cubeTriLinToFun_map_add₁
  cubeTriLinToFun_swap1
  cubeTriLinToFun_swap2
