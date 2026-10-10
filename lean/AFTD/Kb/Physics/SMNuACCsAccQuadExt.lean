import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.SMNuACCsAccQuadDecomp
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMνACCs.accQuad_ext

Topic: quantum_field_theory   Node: 99ed35f6d0c4

Provenance: formalization of a published result. Source: Physlib, `SMνACCs.accQuad_ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extensionality lemma for `accQuad`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνACCs in
open Nat in
open BigOperators in
open SMνCharges in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accQuad`. -/
lemma SMνACCs.accQuad_ext {S T : (SMνCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  rw [accQuad_decomp, accQuad_decomp]
  simp_all
