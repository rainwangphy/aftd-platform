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
import AFTD.Kb.Physics.MSSMACCsAccSU2
import AFTD.Kb.Physics.MSSMChargesQ
import AFTD.Kb.Physics.MSSMChargesL
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# MSSMACCs.accSU2_ext

Topic: quantum_field_theory   Node: 0d7476c4f23d

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.accSU2_ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extensionality lemma for `accSU2`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accSU2`. -/
lemma MSSMACCs.accSU2_ext {S T : MSSMCharges.Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accSU2 S = accSU2 T := by
  simp only [accSU2, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib, ← Finset.mul_sum,
    hj, hd, hu]
