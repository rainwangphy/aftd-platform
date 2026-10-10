import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolToSolAlpha1
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolToSolInv
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolToSolAlpha2
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolToSolInv1
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolToSolAlpha2AF
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
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
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.PlusU1.quadSolToSolInv_α₁_α₂_zero

Topic: quantum_field_theory   Node: f59280ea4c4e

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.quadSolToSolInv_α₁_α₂_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/QuadSolToSol.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.PlusU1.quadSolToSolInv_α₁_α₂_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN.PlusU1.QuadSolToSol in
lemma SMRHN.PlusU1.quadSolToSolInv_α₁_α₂_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 = 0) :
    α₁ (quadSolToSolInv S).1 = 0 ∧ α₂ (quadSolToSolInv S).1 = 0 := by
  rw [quadSolToSolInv_1, α₂_AF S, h]
  exact Prod.mk_eq_zero.mp rfl
