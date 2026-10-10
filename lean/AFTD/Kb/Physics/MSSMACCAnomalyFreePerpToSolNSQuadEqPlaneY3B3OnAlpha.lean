import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpToSolNSQuad
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMACCAlpha1
import AFTD.Kb.Physics.MSSMACCAlpha2
import AFTD.Kb.Physics.MSSMACCAlpha3
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Eq
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.MSSMACCY3
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
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp

/-!
# MSSMACC.AnomalyFreePerp.toSolNSQuad_eq_planeY₃B₃_on_α

Topic: quantum_field_theory   Node: b93236fc69a6

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.toSolNSQuad_eq_planeY₃B₃_on_α`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.toSolNSQuad_eq_planeY₃B₃_on_α
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.AnomalyFreePerp.toSolNSQuad_eq_planeY₃B₃_on_α (R : MSSMACC.AnomalyFreePerp) :
    (toSolNSQuad R).1 = planeY₃B₃ R (α₁ R) (α₂ R) (α₃ R) := by
  change (planeY₃B₃ _ _ _ _) = _
  apply planeY₃B₃_eq
  rw [α₁, α₂, α₃]
  ring_nf
  exact ⟨trivial, trivial, trivial⟩
