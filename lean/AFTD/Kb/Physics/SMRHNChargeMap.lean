import AFTD.Prelude
import AFTD.Kb.Physics.SMRHNPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.SMRHNInstGroupPermGroup

/-!
# SMRHN.chargeMap

Topic: quantum_field_theory   Node: d0cba9fd1dac

Provenance: formalization of a published result. Source: Physlib, `SMRHN.chargeMap`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The image of an element of `permGroup n` under the representation on charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN in
open Nat in
open Finset in
open SMνCharges in
open BigOperators in
variable {n : ℕ} in
/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def SMRHN.chargeMap (f : PermGroup n) : (SMνCharges n).Charges →ₗ[ℚ] (SMνCharges n).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => toSpecies i S ∘ f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
