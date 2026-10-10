import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCLineCube
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMACCAlpha1
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Smul
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.lineCube_smul

Topic: quantum_field_theory   Node: d6e9284af9bb

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.lineCube_smul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/PlaneWithY3B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.lineCube_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.lineCube_smul (R : MSSMACC.AnomalyFreePerp) (a b c d : ℚ) :
    lineCube R (d * a) (d * b) (d * c) = d • lineCube R a b c := by
  apply ACCSystemLinear.LinSols.ext
  change _ = (d • planeY₃B₃ R _ _ _).val
  rw [← planeY₃B₃_smul]
  change (planeY₃B₃ R _ _ _).val = (planeY₃B₃ R _ _ _).val
  ring_nf
