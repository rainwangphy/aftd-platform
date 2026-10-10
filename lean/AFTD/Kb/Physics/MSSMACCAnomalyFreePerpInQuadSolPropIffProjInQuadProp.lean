import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.MSSMACCQuadProj
import AFTD.Kb.Physics.MSSMACCQuadY3Proj
import AFTD.Kb.Physics.MSSMACCQuadB3Proj
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
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# MSSMACC.AnomalyFreePerp.inQuadSolProp_iff_proj_inQuadProp

Topic: quantum_field_theory   Node: a9dc1b982c5b

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inQuadSolProp_iff_proj_inQuadProp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conditions `inQuadSolProp R` and `inQuadProp (proj R.1.1)` are equivalent. This is to be expected since both `R` and `proj R.1.1` define the same plane with `Y₃` and `B₃`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- The conditions `inQuadSolProp R` and `inQuadProp (proj R.1.1)` are equivalent. This is to be expected since both `R` and `proj R.1.1` define the same plane with `Y₃` and `B₃`. -/
lemma MSSMACC.AnomalyFreePerp.inQuadSolProp_iff_proj_inQuadProp (R : MSSMACC.Sols) :
    InQuadSolProp R ↔ InQuadProp (proj R.1.1) := by
  rw [InQuadSolProp, InQuadProp, quad_proj, quad_Y₃_proj, quad_B₃_proj]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [h.1, h.2]
    simp only [mul_zero, add_zero, and_self]
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_self, false_or] at h
    rw [h.2.1, h.2.2]
    exact Prod.mk_eq_zero.mp rfl
