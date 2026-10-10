import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNSM
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB0
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB1
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB2
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB3
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB4
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB5
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB6
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
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
# SMRHN.SM.PlaneSeven.basis_linear_independent

Topic: quantum_field_theory   Node: dc83ff823905

Provenance: formalization of a published result. Source: Physlib, `SMRHN.SM.PlaneSeven.basis_linear_independent`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Ordinary/DimSevenPlane.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.SM.PlaneSeven.basis_linear_independent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open SMνACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
theorem SMRHN.SM.PlaneSeven.basis_linear_independent : LinearIndependent ℚ B := by
  refine Fintype.linearIndependent_iff.mpr fun f h ↦ ?_
  have h0 := congrFun h (0 : Fin 18)
  have h1 := congrFun h (3 : Fin 18)
  have h2 := congrFun h (6 : Fin 18)
  have h3 := congrFun h (9 : Fin 18)
  have h4 := congrFun h (12 : Fin 18)
  have h5 := congrFun h (15 : Fin 18)
  have h6 := congrFun h (5 : Fin 18)
  simp only [Fin.sum_univ_seven, B, B₀, B₁, B₂, B₃, B₄, B₅, B₆, HSMul.hSMul,
    ACCSystemCharges.chargesAddCommMonoid_add, ACCSystemCharges.chargesModule_smul, Fin.isValue,
    Equiv.invFun_as_coe, toSpeciesEquiv_symm_apply, Fin.divNat, Nat.reduceMul, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Nat.zero_div, Fin.zero_eta, Fin.modNat, mul_one, mul_zero, add_zero,
    Nat.reduceMod, Nat.ofNat_pos, Nat.div_self, Fin.mk_one, Nat.mod_self, zero_add,
    Nat.reduceDiv, Fin.reduceFinMk] at h0 h1 h2 h3 h4 h5 h6
  intro i
  fin_cases i <;> assumption
