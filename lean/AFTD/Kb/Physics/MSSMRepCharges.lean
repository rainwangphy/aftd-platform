import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargeMap
import AFTD.Kb.Physics.MSSMPermGroup
import AFTD.Kb.Physics.MSSMInstGroupPermGroup
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.MSSMChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.MSSMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.MSSMChargeMapToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSM.repCharges

Topic: quantum_field_theory   Node: aba852e761f4

Provenance: formalization of a published result. Source: Physlib, `MSSM.repCharges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The representation of `permGroup` acting on the vector space of charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open MSSMCharges in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
/-- The representation of `permGroup` acting on the vector space of charges. -/
@[simp]
def MSSM.repCharges : Representation ℚ PermGroup (MSSMCharges).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    simp only [Module.End.mul_apply]
    rw [chargeMap_toSpecies, chargeMap_toSpecies]
    simp only [Pi.inv_apply]
    rw [chargeMap_toSpecies]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    exact toSMSpecies_toSpecies_inv _ _
