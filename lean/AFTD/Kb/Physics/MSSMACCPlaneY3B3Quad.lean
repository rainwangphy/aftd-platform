import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Val
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuad
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuadAdd
import AFTD.Kb.Physics.MSSMACCLineY3B3Charges
import AFTD.Kb.Physics.MSSMACCLineY3B3ChargesVal
import AFTD.Kb.Physics.MSSMACCLineY3B3ChargesQuad
import AFTD.Kb.Physics.HomogeneousQuadraticMapSmul
import AFTD.Kb.Physics.BiLinearSymmMapAdd1
import AFTD.Kb.Physics.BiLinearSymmMapSmul1
import AFTD.Kb.Physics.BiLinearSymmMapSmul2
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.planeY₃B₃_quad

Topic: quantum_field_theory   Node: c50c0c6ff078

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.planeY₃B₃_quad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/PlaneWithY3B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.planeY₃B₃_quad
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.planeY₃B₃_quad (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) :
    accQuad (planeY₃B₃ R a b c).val = c * (2 * a * quadBiLin Y₃.val R.val
    + 2 * b * quadBiLin B₃.val R.val + c * quadBiLin R.val R.val) := by
  rw [planeY₃B₃_val]
  rw [accQuad, BiLinearSymm.toHomogeneousQuad_add]
  rw [← lineY₃B₃Charges_val, ← accQuad]
  rw [lineY₃B₃Charges_quad]
  rw [lineY₃B₃Charges_val, accQuad]
  rw [quadBiLin.toHomogeneousQuad.map_smul]
  rw [quadBiLin.map_add₁, quadBiLin.map_smul₁, quadBiLin.map_smul₁]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show (BiLinearSymm.toHomogeneousQuad quadBiLin) R.val = quadBiLin R.val R.val by rfl]
  ring
