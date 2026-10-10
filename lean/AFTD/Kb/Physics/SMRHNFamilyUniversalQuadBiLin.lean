import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsQuadBiLin
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.SMNuACCsQuadBiLinDecomp
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMRHNToSpeciesFamilyUniversal
import AFTD.Kb.Physics.SMRHNSumFamilyUniversalTwo
import AFTD.Kb.Physics.SMNuChargesToSpeciesOne
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedSetOne
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMRHN.familyUniversal_quadBiLin

Topic: quantum_field_theory   Node: 58f748eea921

Provenance: formalization of a published result. Source: Physlib, `SMRHN.familyUniversal_quadBiLin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.familyUniversal_quadBiLin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open SMνACCs in
open BigOperators in
lemma SMRHN.familyUniversal_quadBiLin (S : (SMνCharges 1).Charges) (T : (SMνCharges n).Charges) :
    quadBiLin (familyUniversal n S) T =
    S (0 : Fin 6) * ∑ i, Q T i - 2 * S (1 : Fin 6) * ∑ i, U T i + S (2 : Fin 6) *∑ i, D T i -
    S (3 : Fin 6) * ∑ i, L T i + S (4 : Fin 6) * ∑ i, E T i := by
  rw [quadBiLin_decomp]
  repeat rw [sum_familyUniversal_two]
  repeat rw [toSpecies_one]
  simp only [Fin.isValue, toSpecies_apply, add_left_inj, sub_left_inj, sub_right_inj]
  ring
