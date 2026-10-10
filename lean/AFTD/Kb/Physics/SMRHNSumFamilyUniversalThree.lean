import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.SMRHNToSpeciesFamilyUniversal
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.sum_familyUniversal_three

Topic: quantum_field_theory   Node: d3700064ef19

Provenance: formalization of a published result. Source: Physlib, `SMRHN.sum_familyUniversal_three`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.sum_familyUniversal_three
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma SMRHN.sum_familyUniversal_three {n : ℕ} (S : (SMνCharges 1).Charges)
    (T L : (SMνCharges n).Charges) (j : Fin 6) :
    ∑ i, (toSpecies j (familyUniversal n S) i * toSpecies j T i * toSpecies j L i) =
    (toSpecies j S ⟨0, by simp⟩) * ∑ i, toSpecies j T i * toSpecies j L i := by
  simp only [toSpecies_apply, toSpeciesEquiv_apply, Fin.zero_eta,
    Fin.isValue, Nat.reduceMul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · rfl
  · intro i _
    erw [toSpecies_familyUniversal]
    simp only [toSpecies_apply, toSpeciesEquiv_apply, Fin.zero_eta, Fin.isValue, Nat.reduceMul]
    ring
