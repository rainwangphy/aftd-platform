import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.SMNuChargesN
import AFTD.Kb.Physics.TriLinearSymmMk3
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνACCs.cubeTriLin_decomp

Topic: quantum_field_theory   Node: a8043f05319c

Provenance: formalization of a published result. Source: Physlib, `SMνACCs.cubeTriLin_decomp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνACCs.cubeTriLin_decomp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνACCs in
open Nat in
open BigOperators in
open SMνCharges in
variable {n : ℕ} in
lemma SMνACCs.cubeTriLin_decomp (S T R : (SMνCharges n).Charges) :
    cubeTriLin S T R = 6 * ∑ i, (Q S i * Q T i * Q R i) + 3 * ∑ i, (U S i * U T i * U R i) +
      3 * ∑ i, (D S i * D T i * D R i) + 2 * ∑ i, (L S i * L T i * L R i) +
      ∑ i, (E S i * E T i * E R i) + ∑ i, (N S i * N T i * N R i) := by
  rw [cubeTriLin]
  rw [TriLinearSymm.mk₃_toFun_apply_apply]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
