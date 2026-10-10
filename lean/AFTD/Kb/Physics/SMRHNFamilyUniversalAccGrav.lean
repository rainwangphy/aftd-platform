import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuACCsAccGrav
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.SMNuChargesN
import AFTD.Kb.Physics.SMNuACCsAccGravDecomp
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMRHNToSpeciesFamilyUniversal
import AFTD.Kb.Physics.SMRHNSumFamilyUniversalOne
import AFTD.Kb.Physics.SMNuChargesSumOne
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMRHN.familyUniversal_accGrav

Topic: quantum_field_theory   Node: 30916b0c0de3

Provenance: formalization of a published result. Source: Physlib, `SMRHN.familyUniversal_accGrav`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.familyUniversal_accGrav
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open SMνACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma SMRHN.familyUniversal_accGrav (S : (SMνCharges 1).Charges) :
    accGrav (familyUniversal n S) = n * (accGrav S) := by
  rw [accGrav_decomp, accGrav_decomp]
  repeat rw [sum_familyUniversal_one]
  simp only [Fin.isValue, toSpecies_apply, toSpeciesEquiv, Nat.reduceMul, Equiv.symm_trans,
    Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.symm_symm, sum_one]
  ring
