import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsQuadBiLin
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.BiLinearSymmMk2
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedSetOne
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMνACCs.quadBiLin_decomp

Topic: quantum_field_theory   Node: 0d9097794767

Provenance: formalization of a published result. Source: Physlib, `SMνACCs.quadBiLin_decomp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνACCs.quadBiLin_decomp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνACCs in
open Nat in
open BigOperators in
open SMνCharges in
variable {n : ℕ} in
lemma SMνACCs.quadBiLin_decomp (S T : (SMνCharges n).Charges) :
    quadBiLin S T = ∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i +
        ∑ i, D S i * D T i - ∑ i, L S i * L T i + ∑ i, E S i * E T i := by
  rw [quadBiLin]
  rw [BiLinearSymm.mk₂_toFun_apply]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp only [toSpecies_apply, Fin.isValue, neg_mul, one_mul, add_left_inj]
  ring
