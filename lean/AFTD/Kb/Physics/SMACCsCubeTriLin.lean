import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymmMk3
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMChargesU
import AFTD.Kb.Physics.SMChargesD
import AFTD.Kb.Physics.SMChargesL
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMACCs.cubeTriLin

Topic: quantum_field_theory   Node: f14dd32ad5ed

Provenance: formalization of a published result. Source: Physlib, `SMACCs.cubeTriLin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trilinear function defining the cubic.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open SMCharges in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- The trilinear function defining the cubic. -/
@[simps!]
def SMACCs.cubeTriLin : TriLinearSymm (SMCharges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    + ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))))
  (by
    intro a S T R
    simp only
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat rw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T R L
    simp only
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T L
    simp only [toSpecies_apply, Fin.isValue]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S T L
    simp only [toSpecies_apply, Fin.isValue]
    apply Fintype.sum_congr
    intro i
    ring)
