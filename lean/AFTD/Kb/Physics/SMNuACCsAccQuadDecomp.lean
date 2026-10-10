import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsQuadBiLin
import AFTD.Kb.Physics.SMNuACCsQuadBiLinDecomp
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνACCs.accQuad_decomp

Topic: quantum_field_theory   Node: b82635627016

Provenance: formalization of a published result. Source: Physlib, `SMνACCs.accQuad_decomp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνACCs.accQuad_decomp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνACCs in
open Nat in
open BigOperators in
open SMνCharges in
variable {n : ℕ} in
lemma SMνACCs.accQuad_decomp (S : (SMνCharges n).Charges) :
    accQuad S = ∑ i, (Q S i)^2 - 2 * ∑ i, (U S i)^2 + ∑ i, (D S i)^2 - ∑ i, (L S i)^2
    + ∑ i, (E S i)^2 := by
  change (quadBiLin S) S = _
  rw [quadBiLin_decomp]
  ring_nf
