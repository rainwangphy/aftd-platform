import AFTD.Prelude
import AFTD.Kb.Physics.MSSMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.MSSMChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.MSSMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMChargesSplitSMPlusH
import AFTD.Kb.Physics.MSSMChargesToSpeciesMaps'
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.MSSMInstGroupPermGroup

/-!
# MSSM.chargeMap

Topic: quantum_field_theory   Node: f0bcb5dff4c5

Provenance: formalization of a published result. Source: Physlib, `MSSM.chargeMap`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The image of an element of `permGroup` under the representation on charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open MSSMCharges in
open BigOperators in
/-- The image of an element of `permGroup` under the representation on charges. -/
@[simps!]
def MSSM.chargeMap (f : PermGroup) : MSSMCharges.Charges →ₗ[ℚ] MSSMCharges.Charges where
  toFun S := toSpecies.symm (fun i => toSMSpecies i S ∘ f i, Prod.snd (toSpecies S))
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    rw [(toSMSpecies i).map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    apply And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    rw [(toSMSpecies i).map_smul, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
