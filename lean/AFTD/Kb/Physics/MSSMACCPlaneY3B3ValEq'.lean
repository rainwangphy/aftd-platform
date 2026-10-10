import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Val
import AFTD.Kb.Physics.BiLinearSymmMapAdd2
import AFTD.Kb.Physics.BiLinearSymmMapSmul2
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
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.planeY₃B₃_val_eq'

Topic: quantum_field_theory   Node: cf386621b3c2

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.planeY₃B₃_val_eq'`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/PlaneWithY3B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.planeY₃B₃_val_eq'
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.planeY₃B₃_val_eq' (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) (hR' : R.val ≠ 0)
    (h : (planeY₃B₃ R a b c).val = (planeY₃B₃ R a' b' c').val) :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [planeY₃B₃_val, planeY₃B₃_val] at h
  have h1 := congrArg (fun S => dot Y₃.val S) h
  have h2 := congrArg (fun S => dot B₃.val S) h
  simp only [dot.map_add₂, dot.map_smul₂, R.perpY₃, R.perpB₃,
    show dot Y₃.val Y₃.val = 216 by with_unfolding_all rfl,
    show dot B₃.val B₃.val = 108 by with_unfolding_all rfl,
    show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl,
    show dot B₃.val Y₃.val = 108 by with_unfolding_all rfl,
    mul_zero, add_zero] at h1 h2
  have ha : a = a' := by linarith
  have hb : b = b' := by linarith
  rw [ha, hb] at h
  exact ⟨ha, hb, smul_left_injective ℚ hR' (add_left_cancel h)⟩
