import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMChargesQ
import AFTD.Kb.Physics.MSSMChargesU
import AFTD.Kb.Physics.MSSMChargesD
import AFTD.Kb.Physics.MSSMChargesL
import AFTD.Kb.Physics.MSSMChargesE
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmMk2
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuad
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# MSSMACCs.accQuad_ext

Topic: quantum_field_theory   Node: 257927682cf0

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.accQuad_ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extensionality lemma for `accQuad`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accQuad`. -/
lemma MSSMACCs.accQuad_ext {S T : (MSSMCharges).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accQuad S = accQuad T := by
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^2 = ∑ i, (toSMSpecies j T i)^2 := h
  simp only [HomogeneousQuadratic, accQuad, BiLinearSymm.toHomogeneousQuad_apply, quadBiLin,
    BiLinearSymm.mk₂_toFun_apply, ← pow_two, Finset.sum_add_distrib, ← Finset.mul_sum, h1, hd, hu]
