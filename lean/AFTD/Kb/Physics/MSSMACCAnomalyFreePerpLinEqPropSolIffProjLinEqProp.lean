import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqCoeff
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSolIffLineEqCoeffZero
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCAlpha3
import AFTD.Kb.Physics.MSSMACCAlpha1
import AFTD.Kb.Physics.MSSMACCAlpha2
import AFTD.Kb.Physics.MSSMACCAlpha1Proj
import AFTD.Kb.Physics.MSSMACCAlpha2Proj
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# MSSMACC.AnomalyFreePerp.linEqPropSol_iff_proj_linEqProp

Topic: quantum_field_theory   Node: 532f399628eb

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.linEqPropSol_iff_proj_linEqProp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.linEqPropSol_iff_proj_linEqProp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.AnomalyFreePerp.linEqPropSol_iff_proj_linEqProp (R : MSSMACC.Sols) :
    LineEqPropSol R ↔ LineEqProp (proj R.1.1) := by
  rw [lineEqPropSol_iff_lineEqCoeff_zero, lineEqCoeff, LineEqProp]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h
    rw [α₁_proj, α₂_proj, h]
    simp only [neg_zero, zero_mul, and_self]
  · rw [h.2.2]
    exact Rat.mul_zero ((dot Y₃.val) B₃.val)
